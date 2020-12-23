%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gszyf9uTzo

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:57 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  250 (3546 expanded)
%              Number of leaves         :   45 ( 990 expanded)
%              Depth                    :   39
%              Number of atoms          : 1825 (42556 expanded)
%              Number of equality atoms :   27 ( 371 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m2_subset_1_type,type,(
    m2_subset_1: $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v2_tex_2 @ X42 @ X43 )
      | ( X42
        = ( u1_struct_0 @ ( sk_C_2 @ X42 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X28: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ~ ( v7_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('14',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_1 )
      | ~ ( v7_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
      | ~ ( l1_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v2_tex_2 @ X42 @ X43 )
      | ( m1_pre_topc @ ( sk_C_2 @ X42 @ X43 ) @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( m1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( m1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('27',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( l1_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('28',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( l1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('31',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('32',plain,
    ( ( l1_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_1 )
      | ~ ( v7_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','32'])).

thf('34',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('37',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m2_subset_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_m2_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m2_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( m2_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( m2_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m2_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['44','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m2_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X24 @ X22 )
      | ~ ( m2_subset_1 @ X24 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_m2_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m2_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('58',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['58','59'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['62','63'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('65',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X5 ) @ X7 )
      | ~ ( r2_hidden @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('66',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('67',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X40 )
      | ~ ( v1_zfmisc_1 @ X40 )
      | ( X41 = X40 )
      | ~ ( r1_tarski @ X41 @ X40 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['69','70'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('72',plain,(
    ! [X4: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('73',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
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

thf('75',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X38 @ X39 ) @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

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

thf('84',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( X38
        = ( u1_struct_0 @ ( sk_C_1 @ X38 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('98',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['86','95','96','97'])).

thf('99',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('100',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X5 ) @ X7 )
      | ~ ( r2_hidden @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['73','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X38 @ X39 ) )
      | ~ ( l1_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['103','112'])).

thf('114',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('115',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k1_tarski @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ X0 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('119',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('120',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ X32 )
      | ( ( k6_domain_1 @ X32 @ X33 )
        = ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('121',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('123',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['86','95','96','97'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('126',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X45 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X45 ) @ X44 ) @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('127',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['124','131'])).

thf('133',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('135',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('137',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['34'])).

thf('143',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('145',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['35','143','144'])).

thf('146',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['33','145'])).

thf('147',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['34'])).

thf('148',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['35','143'])).

thf('149',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v7_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['146','149'])).

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

thf('151',plain,(
    ! [X35: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( v1_tdlat_3 @ X35 )
      | ~ ( v2_tdlat_3 @ X35 )
      | ( v7_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('152',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v2_tex_2 @ X42 @ X43 )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ X42 @ X43 ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('159',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['35','143','144'])).

thf('160',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['157','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,
    ( ~ ( l1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['151','165'])).

thf('167',plain,
    ( ( l1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('168',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['35','143','144'])).

thf('169',plain,(
    l1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( m1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(cc6_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_tdlat_3 @ B ) ) ) )).

thf('171',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_pre_topc @ X36 @ X37 )
      | ( v2_tdlat_3 @ X36 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_tdlat_3 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('172',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['172','173','174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v2_tdlat_3 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['35','143','144'])).

thf('180',plain,(
    v2_tdlat_3 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('182',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v2_tex_2 @ X42 @ X43 )
      | ( v1_tdlat_3 @ ( sk_C_2 @ X42 @ X43 ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['181','187'])).

thf('189',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v1_tdlat_3 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['35','143','144'])).

thf('194',plain,(
    v1_tdlat_3 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( l1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(cc2_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('196',plain,(
    ! [X34: $i] :
      ( ~ ( v2_tdlat_3 @ X34 )
      | ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc2_tdlat_3])).

thf('197',plain,
    ( ( ( v2_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( v2_tdlat_3 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('199',plain,
    ( ( v2_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['35','143','144'])).

thf('201',plain,(
    v2_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['199','200'])).

thf('202',plain,(
    v7_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['166','169','180','194','201'])).

thf('203',plain,(
    $false ),
    inference(demod,[status(thm)],['150','202'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gszyf9uTzo
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:18:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 514 iterations in 0.162s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.43/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.61  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.43/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.61  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.43/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.43/0.61  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.43/0.61  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.43/0.61  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.43/0.61  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.43/0.61  thf(m2_subset_1_type, type, m2_subset_1: $i > $i > $i > $o).
% 0.43/0.61  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.43/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.43/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.61  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.43/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.43/0.61  thf(t44_tex_2, conjecture,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.43/0.61         ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.43/0.61             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.61           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i]:
% 0.43/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.43/0.61            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61          ( ![B:$i]:
% 0.43/0.61            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.43/0.61                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.61              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.43/0.61  thf('0', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t34_tex_2, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.43/0.61             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.61           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.43/0.61                ( ![C:$i]:
% 0.43/0.61                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.43/0.61                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.43/0.61                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (![X42 : $i, X43 : $i]:
% 0.43/0.61         ((v1_xboole_0 @ X42)
% 0.43/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.43/0.61          | ~ (v2_tex_2 @ X42 @ X43)
% 0.43/0.61          | ((X42) = (u1_struct_0 @ (sk_C_2 @ X42 @ X43)))
% 0.43/0.61          | ~ (l1_pre_topc @ X43)
% 0.43/0.61          | ~ (v2_pre_topc @ X43)
% 0.43/0.61          | (v2_struct_0 @ X43))),
% 0.43/0.61      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | ((sk_B_1) = (u1_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A)))
% 0.43/0.61        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.61  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ((sk_B_1) = (u1_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A)))
% 0.43/0.61        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.61      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      ((((v1_xboole_0 @ sk_B_1)
% 0.43/0.61         | ((sk_B_1) = (u1_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A)))
% 0.43/0.61         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['1', '7'])).
% 0.43/0.61  thf('9', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      ((((v2_struct_0 @ sk_A)
% 0.43/0.61         | ((sk_B_1) = (u1_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A)))))
% 0.43/0.61         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['8', '9'])).
% 0.43/0.61  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      ((((sk_B_1) = (u1_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))))
% 0.43/0.61         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['10', '11'])).
% 0.43/0.61  thf(fc7_struct_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.43/0.61       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      (![X28 : $i]:
% 0.43/0.61         ((v1_zfmisc_1 @ (u1_struct_0 @ X28))
% 0.43/0.61          | ~ (l1_struct_0 @ X28)
% 0.43/0.61          | ~ (v7_struct_0 @ X28))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      ((((v1_zfmisc_1 @ sk_B_1)
% 0.43/0.61         | ~ (v7_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.43/0.61         | ~ (l1_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))))
% 0.43/0.61         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['12', '13'])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf('16', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (![X42 : $i, X43 : $i]:
% 0.43/0.61         ((v1_xboole_0 @ X42)
% 0.43/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.43/0.61          | ~ (v2_tex_2 @ X42 @ X43)
% 0.43/0.61          | (m1_pre_topc @ (sk_C_2 @ X42 @ X43) @ X43)
% 0.43/0.61          | ~ (l1_pre_topc @ X43)
% 0.43/0.61          | ~ (v2_pre_topc @ X43)
% 0.43/0.61          | (v2_struct_0 @ X43))),
% 0.43/0.61      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (m1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_A)
% 0.43/0.61        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.43/0.61  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (m1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_A)
% 0.43/0.61        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.61      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      ((((v1_xboole_0 @ sk_B_1)
% 0.43/0.61         | (m1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_A)
% 0.43/0.61         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['15', '21'])).
% 0.43/0.61  thf('23', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      ((((v2_struct_0 @ sk_A) | (m1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_A)))
% 0.43/0.61         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['22', '23'])).
% 0.43/0.61  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (((m1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_A))
% 0.43/0.61         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['24', '25'])).
% 0.43/0.61  thf(dt_m1_pre_topc, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( l1_pre_topc @ A ) =>
% 0.43/0.61       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.43/0.61  thf('27', plain,
% 0.43/0.61      (![X26 : $i, X27 : $i]:
% 0.43/0.61         (~ (m1_pre_topc @ X26 @ X27)
% 0.43/0.61          | (l1_pre_topc @ X26)
% 0.43/0.61          | ~ (l1_pre_topc @ X27))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A))))
% 0.43/0.61         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.43/0.61  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('30', plain,
% 0.43/0.61      (((l1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A)))
% 0.43/0.61         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.43/0.61  thf(dt_l1_pre_topc, axiom,
% 0.43/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.43/0.61  thf('32', plain,
% 0.43/0.61      (((l1_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A)))
% 0.43/0.61         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.43/0.61  thf('33', plain,
% 0.43/0.61      ((((v1_zfmisc_1 @ sk_B_1) | ~ (v7_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))))
% 0.43/0.61         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['14', '32'])).
% 0.43/0.61  thf('34', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('35', plain,
% 0.43/0.61      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('split', [status(esa)], ['34'])).
% 0.43/0.61  thf('36', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf(d1_xboole_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.61  thf('37', plain,
% 0.43/0.61      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.61  thf(t1_subset, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.43/0.61  thf('38', plain,
% 0.43/0.61      (![X15 : $i, X16 : $i]:
% 0.43/0.61         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.43/0.61      inference('cnf', [status(esa)], [t1_subset])).
% 0.43/0.61  thf('39', plain,
% 0.43/0.61      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(redefinition_m2_subset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.43/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.43/0.61       ( ![C:$i]: ( ( m2_subset_1 @ C @ A @ B ) <=> ( m1_subset_1 @ C @ B ) ) ) ))).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.43/0.61         ((v1_xboole_0 @ X21)
% 0.43/0.61          | (v1_xboole_0 @ X22)
% 0.43/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 0.43/0.61          | (m2_subset_1 @ X23 @ X21 @ X22)
% 0.43/0.61          | ~ (m1_subset_1 @ X23 @ X22))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_m2_subset_1])).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.43/0.61          | (m2_subset_1 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.43/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.43/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.43/0.61  thf('43', plain,
% 0.43/0.61      (((v1_xboole_0 @ sk_B_1)
% 0.43/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.43/0.62        | (m2_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['39', '42'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (((m2_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.43/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('simplify', [status(thm)], ['43'])).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(cc1_subset_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( v1_xboole_0 @ A ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      (![X13 : $i, X14 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.43/0.62          | (v1_xboole_0 @ X13)
% 0.43/0.62          | ~ (v1_xboole_0 @ X14))),
% 0.43/0.62      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.43/0.62  thf('47', plain,
% 0.43/0.62      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.43/0.62  thf('48', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('49', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('clc', [status(thm)], ['47', '48'])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.43/0.62        | (m2_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.43/0.62      inference('clc', [status(thm)], ['44', '49'])).
% 0.43/0.62  thf('51', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('52', plain,
% 0.43/0.62      ((m2_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_B_1)),
% 0.43/0.62      inference('clc', [status(thm)], ['50', '51'])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('54', plain,
% 0.43/0.62      (![X21 : $i, X22 : $i, X24 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X21)
% 0.43/0.62          | (v1_xboole_0 @ X22)
% 0.43/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 0.43/0.62          | (m1_subset_1 @ X24 @ X22)
% 0.43/0.62          | ~ (m2_subset_1 @ X24 @ X21 @ X22))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_m2_subset_1])).
% 0.43/0.62  thf('55', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (m2_subset_1 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.43/0.62          | (m1_subset_1 @ X0 @ sk_B_1)
% 0.43/0.62          | (v1_xboole_0 @ sk_B_1)
% 0.43/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.43/0.62  thf('56', plain,
% 0.43/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.43/0.62        | (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['52', '55'])).
% 0.43/0.62  thf('57', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('clc', [status(thm)], ['47', '48'])).
% 0.43/0.62  thf('58', plain,
% 0.43/0.62      (((m1_subset_1 @ (sk_B @ sk_B_1) @ sk_B_1) | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('clc', [status(thm)], ['56', '57'])).
% 0.43/0.62  thf('59', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('60', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.43/0.62      inference('clc', [status(thm)], ['58', '59'])).
% 0.43/0.62  thf(t2_subset, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ A @ B ) =>
% 0.43/0.62       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.43/0.62  thf('61', plain,
% 0.43/0.62      (![X17 : $i, X18 : $i]:
% 0.43/0.62         ((r2_hidden @ X17 @ X18)
% 0.43/0.62          | (v1_xboole_0 @ X18)
% 0.43/0.62          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.43/0.62      inference('cnf', [status(esa)], [t2_subset])).
% 0.43/0.62  thf('62', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.43/0.62  thf('63', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('64', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.43/0.62      inference('clc', [status(thm)], ['62', '63'])).
% 0.43/0.62  thf(l1_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.43/0.62  thf('65', plain,
% 0.43/0.62      (![X5 : $i, X7 : $i]:
% 0.43/0.62         ((r1_tarski @ (k1_tarski @ X5) @ X7) | ~ (r2_hidden @ X5 @ X7))),
% 0.43/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.43/0.62  thf('66', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_B_1)),
% 0.43/0.62      inference('sup-', [status(thm)], ['64', '65'])).
% 0.43/0.62  thf(t1_tex_2, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.43/0.62           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.43/0.62  thf('67', plain,
% 0.43/0.62      (![X40 : $i, X41 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X40)
% 0.43/0.62          | ~ (v1_zfmisc_1 @ X40)
% 0.43/0.62          | ((X41) = (X40))
% 0.43/0.62          | ~ (r1_tarski @ X41 @ X40)
% 0.43/0.62          | (v1_xboole_0 @ X41))),
% 0.43/0.62      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.43/0.62  thf('68', plain,
% 0.43/0.62      (((v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))
% 0.43/0.62        | ((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1))
% 0.43/0.62        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.43/0.62  thf('69', plain,
% 0.43/0.62      ((((v1_xboole_0 @ sk_B_1)
% 0.43/0.62         | ((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1))
% 0.43/0.62         | (v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 0.43/0.62         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['36', '68'])).
% 0.43/0.62  thf('70', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('71', plain,
% 0.43/0.62      ((((v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))
% 0.43/0.62         | ((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1))))
% 0.43/0.62         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('clc', [status(thm)], ['69', '70'])).
% 0.43/0.62  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.43/0.62  thf('72', plain, (![X4 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X4))),
% 0.43/0.62      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.43/0.62  thf('73', plain,
% 0.43/0.62      ((((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1)))
% 0.43/0.62         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('clc', [status(thm)], ['71', '72'])).
% 0.43/0.62  thf('74', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(t10_tsep_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.43/0.62             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.62           ( ?[C:$i]:
% 0.43/0.62             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.43/0.62               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.43/0.62  thf('75', plain,
% 0.43/0.62      (![X38 : $i, X39 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X38)
% 0.43/0.62          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.43/0.62          | (m1_pre_topc @ (sk_C_1 @ X38 @ X39) @ X39)
% 0.43/0.62          | ~ (l1_pre_topc @ X39)
% 0.43/0.62          | (v2_struct_0 @ X39))),
% 0.43/0.62      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.43/0.62  thf('76', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['74', '75'])).
% 0.43/0.62  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('78', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('demod', [status(thm)], ['76', '77'])).
% 0.43/0.62  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('80', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.43/0.62        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))),
% 0.43/0.62      inference('clc', [status(thm)], ['78', '79'])).
% 0.43/0.62  thf('81', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('82', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.43/0.62      inference('clc', [status(thm)], ['80', '81'])).
% 0.43/0.62  thf('83', plain,
% 0.43/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.62  thf(t55_pre_topc, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.43/0.62           ( ![C:$i]:
% 0.43/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.43/0.62               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.43/0.62  thf('84', plain,
% 0.43/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X29)
% 0.43/0.62          | ~ (m1_pre_topc @ X29 @ X30)
% 0.43/0.62          | (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.43/0.62          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.43/0.62          | ~ (l1_pre_topc @ X30)
% 0.43/0.62          | (v2_struct_0 @ X30))),
% 0.43/0.62      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.43/0.62  thf('85', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.43/0.62          | (v2_struct_0 @ X1)
% 0.43/0.62          | ~ (l1_pre_topc @ X1)
% 0.43/0.62          | (m1_subset_1 @ (sk_B @ (u1_struct_0 @ X0)) @ (u1_struct_0 @ X1))
% 0.43/0.62          | ~ (m1_pre_topc @ X0 @ X1)
% 0.43/0.62          | (v2_struct_0 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['83', '84'])).
% 0.43/0.62  thf('86', plain,
% 0.43/0.62      (((v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.43/0.62        | (m1_subset_1 @ (sk_B @ (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.43/0.62           (u1_struct_0 @ sk_A))
% 0.43/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | (v1_xboole_0 @ (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['82', '85'])).
% 0.43/0.62  thf('87', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('88', plain,
% 0.43/0.62      (![X38 : $i, X39 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X38)
% 0.43/0.62          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.43/0.62          | ((X38) = (u1_struct_0 @ (sk_C_1 @ X38 @ X39)))
% 0.43/0.62          | ~ (l1_pre_topc @ X39)
% 0.43/0.62          | (v2_struct_0 @ X39))),
% 0.43/0.62      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.43/0.62  thf('89', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['87', '88'])).
% 0.43/0.62  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('91', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('demod', [status(thm)], ['89', '90'])).
% 0.43/0.62  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('93', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.43/0.62        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))),
% 0.43/0.62      inference('clc', [status(thm)], ['91', '92'])).
% 0.43/0.62  thf('94', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('95', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('clc', [status(thm)], ['93', '94'])).
% 0.43/0.62  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('97', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('clc', [status(thm)], ['93', '94'])).
% 0.43/0.62  thf('98', plain,
% 0.43/0.62      (((v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.43/0.62        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('demod', [status(thm)], ['86', '95', '96', '97'])).
% 0.43/0.62  thf('99', plain,
% 0.43/0.62      (![X17 : $i, X18 : $i]:
% 0.43/0.62         ((r2_hidden @ X17 @ X18)
% 0.43/0.62          | (v1_xboole_0 @ X18)
% 0.43/0.62          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.43/0.62      inference('cnf', [status(esa)], [t2_subset])).
% 0.43/0.62  thf('100', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.43/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['98', '99'])).
% 0.43/0.62  thf('101', plain,
% 0.43/0.62      (![X5 : $i, X7 : $i]:
% 0.43/0.62         ((r1_tarski @ (k1_tarski @ X5) @ X7) | ~ (r2_hidden @ X5 @ X7))),
% 0.43/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.43/0.62  thf('102', plain,
% 0.43/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.43/0.62        | (r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['100', '101'])).
% 0.43/0.62  thf('103', plain,
% 0.43/0.62      ((((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.43/0.62         | (v1_xboole_0 @ sk_B_1)
% 0.43/0.62         | (v2_struct_0 @ sk_A)
% 0.43/0.62         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.43/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['73', '102'])).
% 0.43/0.62  thf('104', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('105', plain,
% 0.43/0.62      (![X38 : $i, X39 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X38)
% 0.43/0.62          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.43/0.62          | ~ (v2_struct_0 @ (sk_C_1 @ X38 @ X39))
% 0.43/0.62          | ~ (l1_pre_topc @ X39)
% 0.43/0.62          | (v2_struct_0 @ X39))),
% 0.43/0.62      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.43/0.62  thf('106', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['104', '105'])).
% 0.43/0.62  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('108', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('demod', [status(thm)], ['106', '107'])).
% 0.43/0.62  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('110', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('clc', [status(thm)], ['108', '109'])).
% 0.43/0.62  thf('111', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('112', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('clc', [status(thm)], ['110', '111'])).
% 0.43/0.62  thf('113', plain,
% 0.43/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62         | (v2_struct_0 @ sk_A)
% 0.43/0.62         | (v1_xboole_0 @ sk_B_1)
% 0.43/0.62         | (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.43/0.62         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['103', '112'])).
% 0.43/0.62  thf('114', plain,
% 0.43/0.62      ((((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1)))
% 0.43/0.62         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('clc', [status(thm)], ['71', '72'])).
% 0.43/0.62  thf('115', plain,
% 0.43/0.62      (![X5 : $i, X6 : $i]:
% 0.43/0.62         ((r2_hidden @ X5 @ X6) | ~ (r1_tarski @ (k1_tarski @ X5) @ X6))),
% 0.43/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.43/0.62  thf('116', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          (~ (r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_B @ sk_B_1) @ X0)))
% 0.43/0.62         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.43/0.62  thf('117', plain,
% 0.43/0.62      ((((v1_xboole_0 @ sk_B_1)
% 0.43/0.62         | (v2_struct_0 @ sk_A)
% 0.43/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62         | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.43/0.62         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['113', '116'])).
% 0.43/0.62  thf('118', plain,
% 0.43/0.62      (![X15 : $i, X16 : $i]:
% 0.43/0.62         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.43/0.62      inference('cnf', [status(esa)], [t1_subset])).
% 0.43/0.62  thf('119', plain,
% 0.43/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62         | (v2_struct_0 @ sk_A)
% 0.43/0.62         | (v1_xboole_0 @ sk_B_1)
% 0.43/0.62         | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.43/0.62         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['117', '118'])).
% 0.43/0.62  thf(redefinition_k6_domain_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.43/0.62       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.43/0.62  thf('120', plain,
% 0.43/0.62      (![X32 : $i, X33 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X32)
% 0.43/0.62          | ~ (m1_subset_1 @ X33 @ X32)
% 0.43/0.62          | ((k6_domain_1 @ X32 @ X33) = (k1_tarski @ X33)))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.43/0.62  thf('121', plain,
% 0.43/0.62      ((((v1_xboole_0 @ sk_B_1)
% 0.43/0.62         | (v2_struct_0 @ sk_A)
% 0.43/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62         | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.43/0.62             = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.43/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['119', '120'])).
% 0.43/0.62  thf('122', plain,
% 0.43/0.62      ((((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1)))
% 0.43/0.62         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('clc', [status(thm)], ['71', '72'])).
% 0.43/0.62  thf('123', plain,
% 0.43/0.62      ((((v1_xboole_0 @ sk_B_1)
% 0.43/0.62         | (v2_struct_0 @ sk_A)
% 0.43/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62         | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) = (sk_B_1))
% 0.43/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('demod', [status(thm)], ['121', '122'])).
% 0.43/0.62  thf('124', plain,
% 0.43/0.62      (((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) = (sk_B_1))
% 0.43/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62         | (v2_struct_0 @ sk_A)
% 0.43/0.62         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['123'])).
% 0.43/0.62  thf('125', plain,
% 0.43/0.62      (((v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.43/0.62        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('demod', [status(thm)], ['86', '95', '96', '97'])).
% 0.43/0.62  thf(t36_tex_2, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.62           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.43/0.62  thf('126', plain,
% 0.43/0.62      (![X44 : $i, X45 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X45))
% 0.43/0.62          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X45) @ X44) @ X45)
% 0.43/0.62          | ~ (l1_pre_topc @ X45)
% 0.43/0.62          | ~ (v2_pre_topc @ X45)
% 0.43/0.62          | (v2_struct_0 @ X45))),
% 0.43/0.62      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.43/0.62  thf('127', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.43/0.62           sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['125', '126'])).
% 0.43/0.62  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('130', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.43/0.62           sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.43/0.62  thf('131', plain,
% 0.43/0.62      (((v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.43/0.62         sk_A)
% 0.43/0.62        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('simplify', [status(thm)], ['130'])).
% 0.43/0.62  thf('132', plain,
% 0.43/0.62      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.62         | (v1_xboole_0 @ sk_B_1)
% 0.43/0.62         | (v2_struct_0 @ sk_A)
% 0.43/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62         | (v1_xboole_0 @ sk_B_1)
% 0.43/0.62         | (v2_struct_0 @ sk_A)
% 0.43/0.62         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.43/0.62         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['124', '131'])).
% 0.43/0.62  thf('133', plain,
% 0.43/0.62      ((((v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.43/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62         | (v2_struct_0 @ sk_A)
% 0.43/0.62         | (v1_xboole_0 @ sk_B_1)
% 0.43/0.62         | (v2_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['132'])).
% 0.43/0.62  thf('134', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('clc', [status(thm)], ['110', '111'])).
% 0.43/0.62  thf('135', plain,
% 0.43/0.62      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.62         | (v1_xboole_0 @ sk_B_1)
% 0.43/0.62         | (v2_struct_0 @ sk_A)
% 0.43/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['133', '134'])).
% 0.43/0.62  thf('136', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('clc', [status(thm)], ['47', '48'])).
% 0.43/0.62  thf('137', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A)
% 0.43/0.62         | (v1_xboole_0 @ sk_B_1)
% 0.43/0.62         | (v2_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['135', '136'])).
% 0.43/0.62  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('139', plain,
% 0.43/0.62      ((((v2_tex_2 @ sk_B_1 @ sk_A) | (v1_xboole_0 @ sk_B_1)))
% 0.43/0.62         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('clc', [status(thm)], ['137', '138'])).
% 0.43/0.62  thf('140', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('141', plain,
% 0.43/0.62      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('clc', [status(thm)], ['139', '140'])).
% 0.43/0.62  thf('142', plain,
% 0.43/0.62      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('split', [status(esa)], ['34'])).
% 0.43/0.62  thf('143', plain,
% 0.43/0.62      (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['141', '142'])).
% 0.43/0.62  thf('144', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('145', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['35', '143', '144'])).
% 0.43/0.62  thf('146', plain,
% 0.43/0.62      (((v1_zfmisc_1 @ sk_B_1) | ~ (v7_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['33', '145'])).
% 0.43/0.62  thf('147', plain,
% 0.43/0.62      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.43/0.62      inference('split', [status(esa)], ['34'])).
% 0.43/0.62  thf('148', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['35', '143'])).
% 0.43/0.62  thf('149', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['147', '148'])).
% 0.43/0.62  thf('150', plain, (~ (v7_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('clc', [status(thm)], ['146', '149'])).
% 0.43/0.62  thf(cc2_tex_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( l1_pre_topc @ A ) =>
% 0.43/0.62       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.43/0.62           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 0.43/0.62         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 0.43/0.62  thf('151', plain,
% 0.43/0.62      (![X35 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X35)
% 0.43/0.62          | ~ (v2_pre_topc @ X35)
% 0.43/0.62          | ~ (v1_tdlat_3 @ X35)
% 0.43/0.62          | ~ (v2_tdlat_3 @ X35)
% 0.43/0.62          | (v7_struct_0 @ X35)
% 0.43/0.62          | ~ (l1_pre_topc @ X35))),
% 0.43/0.62      inference('cnf', [status(esa)], [cc2_tex_1])).
% 0.43/0.62  thf('152', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('153', plain,
% 0.43/0.62      (![X42 : $i, X43 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X42)
% 0.43/0.62          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.43/0.62          | ~ (v2_tex_2 @ X42 @ X43)
% 0.43/0.62          | ~ (v2_struct_0 @ (sk_C_2 @ X42 @ X43))
% 0.43/0.62          | ~ (l1_pre_topc @ X43)
% 0.43/0.62          | ~ (v2_pre_topc @ X43)
% 0.43/0.62          | (v2_struct_0 @ X43))),
% 0.43/0.62      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.43/0.62  thf('154', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62        | ~ (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.43/0.62        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['152', '153'])).
% 0.43/0.62  thf('155', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('156', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('157', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | ~ (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.43/0.62        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('demod', [status(thm)], ['154', '155', '156'])).
% 0.43/0.62  thf('158', plain,
% 0.43/0.62      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('159', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['35', '143', '144'])).
% 0.43/0.62  thf('160', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['158', '159'])).
% 0.43/0.62  thf('161', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | ~ (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('demod', [status(thm)], ['157', '160'])).
% 0.43/0.62  thf('162', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('163', plain,
% 0.43/0.62      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('clc', [status(thm)], ['161', '162'])).
% 0.43/0.62  thf('164', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('165', plain, (~ (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('clc', [status(thm)], ['163', '164'])).
% 0.43/0.62  thf('166', plain,
% 0.43/0.62      ((~ (l1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.43/0.62        | (v7_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.43/0.62        | ~ (v2_tdlat_3 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.43/0.62        | ~ (v1_tdlat_3 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.43/0.62        | ~ (v2_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['151', '165'])).
% 0.43/0.62  thf('167', plain,
% 0.43/0.62      (((l1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A)))
% 0.43/0.62         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.43/0.62  thf('168', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['35', '143', '144'])).
% 0.43/0.62  thf('169', plain, ((l1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['167', '168'])).
% 0.43/0.62  thf('170', plain,
% 0.43/0.62      (((m1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_A))
% 0.43/0.62         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('clc', [status(thm)], ['24', '25'])).
% 0.43/0.62  thf(cc6_tdlat_3, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.43/0.62         ( l1_pre_topc @ A ) ) =>
% 0.43/0.62       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.43/0.62  thf('171', plain,
% 0.43/0.62      (![X36 : $i, X37 : $i]:
% 0.43/0.62         (~ (m1_pre_topc @ X36 @ X37)
% 0.43/0.62          | (v2_tdlat_3 @ X36)
% 0.43/0.62          | ~ (l1_pre_topc @ X37)
% 0.43/0.62          | ~ (v2_tdlat_3 @ X37)
% 0.43/0.62          | ~ (v2_pre_topc @ X37)
% 0.43/0.62          | (v2_struct_0 @ X37))),
% 0.43/0.62      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.43/0.62  thf('172', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A)
% 0.43/0.62         | ~ (v2_pre_topc @ sk_A)
% 0.43/0.62         | ~ (v2_tdlat_3 @ sk_A)
% 0.43/0.62         | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62         | (v2_tdlat_3 @ (sk_C_2 @ sk_B_1 @ sk_A))))
% 0.43/0.62         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['170', '171'])).
% 0.43/0.62  thf('173', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('174', plain, ((v2_tdlat_3 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('176', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C_2 @ sk_B_1 @ sk_A))))
% 0.43/0.62         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['172', '173', '174', '175'])).
% 0.43/0.62  thf('177', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('178', plain,
% 0.43/0.62      (((v2_tdlat_3 @ (sk_C_2 @ sk_B_1 @ sk_A)))
% 0.43/0.62         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('clc', [status(thm)], ['176', '177'])).
% 0.43/0.62  thf('179', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['35', '143', '144'])).
% 0.43/0.62  thf('180', plain, ((v2_tdlat_3 @ (sk_C_2 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['178', '179'])).
% 0.43/0.62  thf('181', plain,
% 0.43/0.62      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('182', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('183', plain,
% 0.43/0.62      (![X42 : $i, X43 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X42)
% 0.43/0.62          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.43/0.62          | ~ (v2_tex_2 @ X42 @ X43)
% 0.43/0.62          | (v1_tdlat_3 @ (sk_C_2 @ X42 @ X43))
% 0.43/0.62          | ~ (l1_pre_topc @ X43)
% 0.43/0.62          | ~ (v2_pre_topc @ X43)
% 0.43/0.62          | (v2_struct_0 @ X43))),
% 0.43/0.62      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.43/0.62  thf('184', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62        | (v1_tdlat_3 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.43/0.62        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['182', '183'])).
% 0.43/0.62  thf('185', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('186', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('187', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (v1_tdlat_3 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.43/0.62        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.62        | (v1_xboole_0 @ sk_B_1))),
% 0.43/0.62      inference('demod', [status(thm)], ['184', '185', '186'])).
% 0.43/0.62  thf('188', plain,
% 0.43/0.62      ((((v1_xboole_0 @ sk_B_1)
% 0.43/0.62         | (v1_tdlat_3 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.43/0.62         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['181', '187'])).
% 0.43/0.62  thf('189', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('190', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_2 @ sk_B_1 @ sk_A))))
% 0.43/0.62         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('clc', [status(thm)], ['188', '189'])).
% 0.43/0.62  thf('191', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('192', plain,
% 0.43/0.62      (((v1_tdlat_3 @ (sk_C_2 @ sk_B_1 @ sk_A)))
% 0.43/0.62         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('clc', [status(thm)], ['190', '191'])).
% 0.43/0.62  thf('193', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['35', '143', '144'])).
% 0.43/0.62  thf('194', plain, ((v1_tdlat_3 @ (sk_C_2 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['192', '193'])).
% 0.43/0.62  thf('195', plain,
% 0.43/0.62      (((l1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A)))
% 0.43/0.62         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.43/0.62  thf(cc2_tdlat_3, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( l1_pre_topc @ A ) => ( ( v2_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.43/0.62  thf('196', plain,
% 0.43/0.62      (![X34 : $i]:
% 0.43/0.62         (~ (v2_tdlat_3 @ X34) | (v2_pre_topc @ X34) | ~ (l1_pre_topc @ X34))),
% 0.43/0.62      inference('cnf', [status(esa)], [cc2_tdlat_3])).
% 0.43/0.62  thf('197', plain,
% 0.43/0.62      ((((v2_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.43/0.62         | ~ (v2_tdlat_3 @ (sk_C_2 @ sk_B_1 @ sk_A))))
% 0.43/0.62         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['195', '196'])).
% 0.43/0.62  thf('198', plain,
% 0.43/0.62      (((v2_tdlat_3 @ (sk_C_2 @ sk_B_1 @ sk_A)))
% 0.43/0.62         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('clc', [status(thm)], ['176', '177'])).
% 0.43/0.62  thf('199', plain,
% 0.43/0.62      (((v2_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A)))
% 0.43/0.62         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['197', '198'])).
% 0.43/0.62  thf('200', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['35', '143', '144'])).
% 0.43/0.62  thf('201', plain, ((v2_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['199', '200'])).
% 0.43/0.62  thf('202', plain, ((v7_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['166', '169', '180', '194', '201'])).
% 0.43/0.62  thf('203', plain, ($false), inference('demod', [status(thm)], ['150', '202'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
