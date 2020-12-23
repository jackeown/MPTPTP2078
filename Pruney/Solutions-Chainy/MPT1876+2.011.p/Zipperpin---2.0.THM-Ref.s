%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FuyMDfaQuC

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 440 expanded)
%              Number of leaves         :   41 ( 139 expanded)
%              Depth                    :   18
%              Number of atoms          : 1111 (5040 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_tex_2 @ X30 @ X31 )
      | ( X30
        = ( u1_struct_0 @ ( sk_C @ X30 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
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
    ! [X20: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ~ ( v7_struct_0 @ X20 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_tex_2 @ X30 @ X31 )
      | ( m1_pre_topc @ ( sk_C @ X30 @ X31 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    ! [X25: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( v1_tdlat_3 @ X25 )
      | ~ ( v2_tdlat_3 @ X25 )
      | ( v7_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('34',plain,
    ( ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
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
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_tex_2 @ X30 @ X31 )
      | ( v1_tdlat_3 @ ( sk_C @ X30 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
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
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','46'])).

thf('48',plain,
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

thf('49',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_tdlat_3 @ X26 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_tdlat_3 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('50',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
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
      | ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(cc1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('58',plain,(
    ! [X23: $i] :
      ( ~ ( v1_tdlat_3 @ X23 )
      | ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc1_tdlat_3])).

thf('59',plain,
    ( ( ( v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('61',plain,
    ( ( v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['47','56','61'])).

thf(cc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( v2_struct_0 @ A )
       => ( v7_struct_0 @ A ) ) ) )).

thf('63',plain,(
    ! [X16: $i] :
      ( ~ ( v2_struct_0 @ X16 )
      | ( v7_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_struct_0])).

thf('64',plain,
    ( ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('66',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,
    ( ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('71',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','69','70'])).

thf('72',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('75',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('76',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('77',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X7 ) @ X9 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('79',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v1_zfmisc_1 @ X28 )
      | ( X29 = X28 )
      | ~ ( r1_tarski @ X29 @ X28 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('82',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('85',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('88',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k1_tarski @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('94',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('95',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( m1_subset_1 @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('97',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('99',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X33 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X33 ) @ X32 ) @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('104',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( ( k6_domain_1 @ X21 @ X22 )
        = ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('105',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('108',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['105','108'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['100','101','102','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['83','112'])).

thf('114',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','115'])).

thf('117',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('118',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','73','74','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FuyMDfaQuC
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:42:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 250 iterations in 0.126s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.58  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.21/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.58  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.58  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.58  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.21/0.58  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(t44_tex_2, conjecture,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.58         ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.58           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i]:
% 0.21/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.58            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58          ( ![B:$i]:
% 0.21/0.58            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.58                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.58              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.21/0.58  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.58      inference('split', [status(esa)], ['2'])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t34_tex_2, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.58           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.58                ( ![C:$i]:
% 0.21/0.58                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.21/0.58                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.58                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X30 : $i, X31 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ X30)
% 0.21/0.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.21/0.58          | ~ (v2_tex_2 @ X30 @ X31)
% 0.21/0.58          | ((X30) = (u1_struct_0 @ (sk_C @ X30 @ X31)))
% 0.21/0.58          | ~ (l1_pre_topc @ X31)
% 0.21/0.58          | ~ (v2_pre_topc @ X31)
% 0.21/0.58          | (v2_struct_0 @ X31))),
% 0.21/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.58      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.58         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['3', '9'])).
% 0.21/0.58  thf('11', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      ((((v2_struct_0 @ sk_A)
% 0.21/0.58         | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))))
% 0.21/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.58      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.58  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      ((((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.21/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.58      inference('clc', [status(thm)], ['12', '13'])).
% 0.21/0.58  thf(fc7_struct_0, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.58       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (![X20 : $i]:
% 0.21/0.58         ((v1_zfmisc_1 @ (u1_struct_0 @ X20))
% 0.21/0.58          | ~ (l1_struct_0 @ X20)
% 0.21/0.58          | ~ (v7_struct_0 @ X20))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      ((((v1_zfmisc_1 @ sk_B_1)
% 0.21/0.58         | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.58         | ~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.21/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.58      inference('split', [status(esa)], ['2'])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (![X30 : $i, X31 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ X30)
% 0.21/0.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.21/0.58          | ~ (v2_tex_2 @ X30 @ X31)
% 0.21/0.58          | (m1_pre_topc @ (sk_C @ X30 @ X31) @ X31)
% 0.21/0.58          | ~ (l1_pre_topc @ X31)
% 0.21/0.58          | ~ (v2_pre_topc @ X31)
% 0.21/0.58          | (v2_struct_0 @ X31))),
% 0.21/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.58      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.58         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['17', '23'])).
% 0.21/0.58  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      ((((v2_struct_0 @ sk_A) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)))
% 0.21/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.58      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.58  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))
% 0.21/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.58      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.58  thf(dt_m1_pre_topc, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_pre_topc @ A ) =>
% 0.21/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      (![X18 : $i, X19 : $i]:
% 0.21/0.58         (~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.58          | (l1_pre_topc @ X18)
% 0.21/0.58          | ~ (l1_pre_topc @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))))
% 0.21/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.58  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.58  thf(cc2_tex_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_pre_topc @ A ) =>
% 0.21/0.58       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.58           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 0.21/0.58         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      (![X25 : $i]:
% 0.21/0.58         ((v2_struct_0 @ X25)
% 0.21/0.58          | ~ (v2_pre_topc @ X25)
% 0.21/0.58          | ~ (v1_tdlat_3 @ X25)
% 0.21/0.58          | ~ (v2_tdlat_3 @ X25)
% 0.21/0.58          | (v7_struct_0 @ X25)
% 0.21/0.58          | ~ (l1_pre_topc @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc2_tex_1])).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      ((((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.58         | ~ (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.58         | ~ (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.58         | ~ (v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.21/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.58      inference('split', [status(esa)], ['2'])).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('37', plain,
% 0.21/0.58      (![X30 : $i, X31 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ X30)
% 0.21/0.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.21/0.58          | ~ (v2_tex_2 @ X30 @ X31)
% 0.21/0.58          | (v1_tdlat_3 @ (sk_C @ X30 @ X31))
% 0.21/0.58          | ~ (l1_pre_topc @ X31)
% 0.21/0.58          | ~ (v2_pre_topc @ X31)
% 0.21/0.58          | (v2_struct_0 @ X31))),
% 0.21/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.58  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.58      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['35', '41'])).
% 0.21/0.58  thf('43', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('44', plain,
% 0.21/0.59      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('clc', [status(thm)], ['42', '43'])).
% 0.21/0.59  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('46', plain,
% 0.21/0.59      (((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('clc', [status(thm)], ['44', '45'])).
% 0.21/0.59  thf('47', plain,
% 0.21/0.59      ((((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.59         | ~ (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.59         | ~ (v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.59         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('demod', [status(thm)], ['34', '46'])).
% 0.21/0.59  thf('48', plain,
% 0.21/0.59      (((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.59  thf(cc6_tdlat_3, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.59         ( l1_pre_topc @ A ) ) =>
% 0.21/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.21/0.59  thf('49', plain,
% 0.21/0.59      (![X26 : $i, X27 : $i]:
% 0.21/0.59         (~ (m1_pre_topc @ X26 @ X27)
% 0.21/0.59          | (v2_tdlat_3 @ X26)
% 0.21/0.59          | ~ (l1_pre_topc @ X27)
% 0.21/0.59          | ~ (v2_tdlat_3 @ X27)
% 0.21/0.59          | ~ (v2_pre_topc @ X27)
% 0.21/0.59          | (v2_struct_0 @ X27))),
% 0.21/0.59      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.21/0.59  thf('50', plain,
% 0.21/0.59      ((((v2_struct_0 @ sk_A)
% 0.21/0.59         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.59         | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.59         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.59         | (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.59  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('52', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('54', plain,
% 0.21/0.59      ((((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.21/0.59  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('56', plain,
% 0.21/0.59      (((v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('clc', [status(thm)], ['54', '55'])).
% 0.21/0.59  thf('57', plain,
% 0.21/0.59      (((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.59  thf(cc1_tdlat_3, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( l1_pre_topc @ A ) => ( ( v1_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.21/0.59  thf('58', plain,
% 0.21/0.59      (![X23 : $i]:
% 0.21/0.59         (~ (v1_tdlat_3 @ X23) | (v2_pre_topc @ X23) | ~ (l1_pre_topc @ X23))),
% 0.21/0.59      inference('cnf', [status(esa)], [cc1_tdlat_3])).
% 0.21/0.59  thf('59', plain,
% 0.21/0.59      ((((v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.59         | ~ (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.59  thf('60', plain,
% 0.21/0.59      (((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('clc', [status(thm)], ['44', '45'])).
% 0.21/0.59  thf('61', plain,
% 0.21/0.59      (((v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.59  thf('62', plain,
% 0.21/0.59      ((((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.59         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('demod', [status(thm)], ['47', '56', '61'])).
% 0.21/0.59  thf(cc1_struct_0, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( l1_struct_0 @ A ) => ( ( v2_struct_0 @ A ) => ( v7_struct_0 @ A ) ) ))).
% 0.21/0.59  thf('63', plain,
% 0.21/0.59      (![X16 : $i]:
% 0.21/0.59         (~ (v2_struct_0 @ X16) | (v7_struct_0 @ X16) | ~ (l1_struct_0 @ X16))),
% 0.21/0.59      inference('cnf', [status(esa)], [cc1_struct_0])).
% 0.21/0.59  thf('64', plain,
% 0.21/0.59      ((((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.59         | ~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.59         | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.59  thf('65', plain,
% 0.21/0.59      (((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.59  thf(dt_l1_pre_topc, axiom,
% 0.21/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.59  thf('66', plain,
% 0.21/0.59      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.59  thf('67', plain,
% 0.21/0.59      (((l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.59  thf('68', plain,
% 0.21/0.59      ((((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.59         | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('demod', [status(thm)], ['64', '67'])).
% 0.21/0.59  thf('69', plain,
% 0.21/0.59      (((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['68'])).
% 0.21/0.59  thf('70', plain,
% 0.21/0.59      (((l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.59  thf('71', plain,
% 0.21/0.59      (((v1_zfmisc_1 @ sk_B_1)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('demod', [status(thm)], ['16', '69', '70'])).
% 0.21/0.59  thf('72', plain,
% 0.21/0.59      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.59      inference('split', [status(esa)], ['0'])).
% 0.21/0.59  thf('73', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.59  thf('74', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.59      inference('split', [status(esa)], ['2'])).
% 0.21/0.59  thf('75', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.59      inference('split', [status(esa)], ['2'])).
% 0.21/0.59  thf(d1_xboole_0, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.59  thf('76', plain,
% 0.21/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.59  thf(l1_zfmisc_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.59  thf('77', plain,
% 0.21/0.59      (![X7 : $i, X9 : $i]:
% 0.21/0.59         ((r1_tarski @ (k1_tarski @ X7) @ X9) | ~ (r2_hidden @ X7 @ X9))),
% 0.21/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.59  thf('78', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.59  thf(t1_tex_2, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.59       ( ![B:$i]:
% 0.21/0.59         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.59           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.59  thf('79', plain,
% 0.21/0.59      (![X28 : $i, X29 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ X28)
% 0.21/0.59          | ~ (v1_zfmisc_1 @ X28)
% 0.21/0.59          | ((X29) = (X28))
% 0.21/0.59          | ~ (r1_tarski @ X29 @ X28)
% 0.21/0.59          | (v1_xboole_0 @ X29))),
% 0.21/0.59      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.21/0.59  thf('80', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ X0)
% 0.21/0.59          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.21/0.59          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.21/0.59          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.59          | (v1_xboole_0 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.59  thf('81', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (v1_zfmisc_1 @ X0)
% 0.21/0.59          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.21/0.59          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.21/0.59          | (v1_xboole_0 @ X0))),
% 0.21/0.59      inference('simplify', [status(thm)], ['80'])).
% 0.21/0.59  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.21/0.59  thf('82', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X6))),
% 0.21/0.59      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.21/0.59  thf('83', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ X0)
% 0.21/0.59          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.21/0.59          | ~ (v1_zfmisc_1 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.59  thf('84', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(t3_subset, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.59  thf('85', plain,
% 0.21/0.59      (![X13 : $i, X14 : $i]:
% 0.21/0.59         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.59  thf('86', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.59  thf('87', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.59  thf(t1_xboole_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.59       ( r1_tarski @ A @ C ) ))).
% 0.21/0.59  thf('88', plain,
% 0.21/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.59         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.59          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.59          | (r1_tarski @ X3 @ X5))),
% 0.21/0.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.59  thf('89', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ X0)
% 0.21/0.59          | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X1)
% 0.21/0.59          | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.59      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.59  thf('90', plain,
% 0.21/0.59      (((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ (u1_struct_0 @ sk_A))
% 0.21/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.59      inference('sup-', [status(thm)], ['86', '89'])).
% 0.21/0.59  thf('91', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('92', plain,
% 0.21/0.59      ((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ (u1_struct_0 @ sk_A))),
% 0.21/0.59      inference('clc', [status(thm)], ['90', '91'])).
% 0.21/0.59  thf('93', plain,
% 0.21/0.59      (![X7 : $i, X8 : $i]:
% 0.21/0.59         ((r2_hidden @ X7 @ X8) | ~ (r1_tarski @ (k1_tarski @ X7) @ X8))),
% 0.21/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.59  thf('94', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['92', '93'])).
% 0.21/0.59  thf(d2_subset_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.59       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.59  thf('95', plain,
% 0.21/0.59      (![X10 : $i, X11 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X10 @ X11)
% 0.21/0.59          | (m1_subset_1 @ X10 @ X11)
% 0.21/0.59          | (v1_xboole_0 @ X11))),
% 0.21/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.59  thf('96', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.59  thf('97', plain,
% 0.21/0.59      (![X10 : $i, X11 : $i]:
% 0.21/0.59         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.21/0.59      inference('clc', [status(thm)], ['95', '96'])).
% 0.21/0.59  thf('98', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['94', '97'])).
% 0.21/0.59  thf(t36_tex_2, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.59       ( ![B:$i]:
% 0.21/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.59           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.21/0.59  thf('99', plain,
% 0.21/0.59      (![X32 : $i, X33 : $i]:
% 0.21/0.59         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X33))
% 0.21/0.59          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X33) @ X32) @ X33)
% 0.21/0.59          | ~ (l1_pre_topc @ X33)
% 0.21/0.59          | ~ (v2_pre_topc @ X33)
% 0.21/0.59          | (v2_struct_0 @ X33))),
% 0.21/0.59      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.21/0.59  thf('100', plain,
% 0.21/0.59      (((v2_struct_0 @ sk_A)
% 0.21/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.59        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.59           sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['98', '99'])).
% 0.21/0.59  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('103', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['94', '97'])).
% 0.21/0.59  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.59       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.59  thf('104', plain,
% 0.21/0.59      (![X21 : $i, X22 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ X21)
% 0.21/0.59          | ~ (m1_subset_1 @ X22 @ X21)
% 0.21/0.59          | ((k6_domain_1 @ X21 @ X22) = (k1_tarski @ X22)))),
% 0.21/0.59      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.59  thf('105', plain,
% 0.21/0.59      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.21/0.59          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.21/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['103', '104'])).
% 0.21/0.59  thf('106', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['92', '93'])).
% 0.21/0.59  thf('107', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.59  thf('108', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['106', '107'])).
% 0.21/0.59  thf('109', plain,
% 0.21/0.59      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.21/0.59         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.21/0.59      inference('clc', [status(thm)], ['105', '108'])).
% 0.21/0.59  thf('110', plain,
% 0.21/0.59      (((v2_struct_0 @ sk_A)
% 0.21/0.59        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.21/0.59      inference('demod', [status(thm)], ['100', '101', '102', '109'])).
% 0.21/0.59  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('112', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.21/0.59      inference('clc', [status(thm)], ['110', '111'])).
% 0.21/0.59  thf('113', plain,
% 0.21/0.59      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.59        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.59      inference('sup+', [status(thm)], ['83', '112'])).
% 0.21/0.59  thf('114', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('115', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.59      inference('clc', [status(thm)], ['113', '114'])).
% 0.21/0.59  thf('116', plain,
% 0.21/0.59      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['75', '115'])).
% 0.21/0.59  thf('117', plain,
% 0.21/0.59      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.59      inference('split', [status(esa)], ['0'])).
% 0.21/0.59  thf('118', plain,
% 0.21/0.59      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['116', '117'])).
% 0.21/0.59  thf('119', plain, ($false),
% 0.21/0.59      inference('sat_resolution*', [status(thm)], ['1', '73', '74', '118'])).
% 0.21/0.59  
% 0.21/0.59  % SZS output end Refutation
% 0.21/0.59  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
