%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gGz2pRgHZu

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:58 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  209 (1975 expanded)
%              Number of leaves         :   39 ( 571 expanded)
%              Depth                    :   41
%              Number of atoms          : 1425 (20327 expanded)
%              Number of equality atoms :   34 ( 299 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

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

thf('0',plain,(
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

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ~ ( v2_struct_0 @ ( sk_C @ X27 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_zfmisc_1 @ X25 )
      | ( X26 = X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('31',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('32',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('43',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['43','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('52',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( m1_subset_1 @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','54'])).

thf('56',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('57',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('59',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('61',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) )
    = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['30','61'])).

thf('63',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['43','48'])).

thf('64',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('69',plain,
    ( ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('71',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
      | ~ ( v1_zfmisc_1 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['28','71'])).

thf('73',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('74',plain,
    ( ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_zfmisc_1 @ X25 )
      | ( X26 = X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('80',plain,
    ( ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 )
      | ~ ( v1_zfmisc_1 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('82',plain,
    ( ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('84',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('88',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X30 ) @ X29 ) @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['43','48'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['86','95'])).

thf('97',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('98',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('100',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','98','99'])).

thf('101',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( m1_pre_topc @ ( sk_C @ X27 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','100'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['116','117'])).

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

thf('119',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( v1_tdlat_3 @ X23 )
      | ( v7_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_tdlat_3 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc32_tex_2])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('125',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( v1_tdlat_3 @ ( sk_C @ X27 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['124','130'])).

thf('132',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','98','99'])).

thf('137',plain,(
    v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( X27
        = ( u1_struct_0 @ ( sk_C @ X27 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','100'])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('153',plain,(
    ! [X17: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ~ ( v7_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('154',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('156',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['9','98'])).

thf('157',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['155','156'])).

thf('158',plain,
    ( ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['154','157'])).

thf('159',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['116','117'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('160',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('161',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['161','162'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('164',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('165',plain,(
    l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['158','165'])).

thf('167',plain,(
    v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['140','166'])).

thf('168',plain,(
    $false ),
    inference(demod,[status(thm)],['106','167'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gGz2pRgHZu
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 252 iterations in 0.113s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.58  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.37/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.58  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.37/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.58  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.37/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.37/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.58  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.37/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.58  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.37/0.58  thf(t44_tex_2, conjecture,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.37/0.58         ( l1_pre_topc @ A ) ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i]:
% 0.37/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.58            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.58          ( ![B:$i]:
% 0.37/0.58            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.58                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t34_tex_2, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.37/0.58                ( ![C:$i]:
% 0.37/0.58                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.37/0.58                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.37/0.58                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      (![X27 : $i, X28 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X27)
% 0.37/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.37/0.58          | ~ (v2_tex_2 @ X27 @ X28)
% 0.37/0.58          | ~ (v2_struct_0 @ (sk_C @ X27 @ X28))
% 0.37/0.58          | ~ (l1_pre_topc @ X28)
% 0.37/0.58          | ~ (v2_pre_topc @ X28)
% 0.37/0.58          | (v2_struct_0 @ X28))),
% 0.37/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.58  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.37/0.58  thf('6', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('split', [status(esa)], ['6'])).
% 0.37/0.58  thf('8', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('split', [status(esa)], ['8'])).
% 0.37/0.58  thf(d1_xboole_0, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.37/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.58  thf(t1_subset, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.37/0.58  thf('11', plain,
% 0.37/0.58      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.37/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.58  thf(redefinition_k6_domain_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.37/0.58       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.37/0.58  thf('13', plain,
% 0.37/0.58      (![X20 : $i, X21 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X20)
% 0.37/0.58          | ~ (m1_subset_1 @ X21 @ X20)
% 0.37/0.58          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.37/0.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X0)
% 0.37/0.58          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.37/0.58          | (v1_xboole_0 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.37/0.58          | (v1_xboole_0 @ X0))),
% 0.37/0.58      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.58  thf(dt_k6_domain_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.37/0.58       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      (![X18 : $i, X19 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X18)
% 0.37/0.58          | ~ (m1_subset_1 @ X19 @ X18)
% 0.37/0.58          | (m1_subset_1 @ (k6_domain_1 @ X18 @ X19) @ (k1_zfmisc_1 @ X18)))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X0)
% 0.37/0.58          | (m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ 
% 0.37/0.58             (k1_zfmisc_1 @ X0))
% 0.37/0.58          | (v1_xboole_0 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.37/0.58          | (v1_xboole_0 @ X0))),
% 0.37/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.37/0.58          | (v1_xboole_0 @ X0)
% 0.37/0.58          | (v1_xboole_0 @ X0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['15', '19'])).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X0)
% 0.37/0.58          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['20'])).
% 0.37/0.58  thf(t3_subset, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      (![X8 : $i, X9 : $i]:
% 0.37/0.58         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.58  thf(t1_tex_2, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.37/0.58           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      (![X25 : $i, X26 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X25)
% 0.37/0.58          | ~ (v1_zfmisc_1 @ X25)
% 0.37/0.58          | ((X26) = (X25))
% 0.37/0.58          | ~ (r1_tarski @ X26 @ X25)
% 0.37/0.58          | (v1_xboole_0 @ X26))),
% 0.37/0.58      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X0)
% 0.37/0.58          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.37/0.58          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.37/0.58          | ~ (v1_zfmisc_1 @ X0)
% 0.37/0.58          | (v1_xboole_0 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.58  thf('26', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (v1_zfmisc_1 @ X0)
% 0.37/0.58          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.37/0.58          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.37/0.58          | (v1_xboole_0 @ X0))),
% 0.37/0.58      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.58  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.37/0.58  thf('27', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X3))),
% 0.37/0.58      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.37/0.58  thf('28', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X0)
% 0.37/0.58          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.37/0.58          | ~ (v1_zfmisc_1 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.58  thf('29', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('split', [status(esa)], ['6'])).
% 0.37/0.58  thf('30', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X0)
% 0.37/0.58          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.37/0.58          | ~ (v1_zfmisc_1 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.37/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.37/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.58  thf('33', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t4_subset, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.37/0.58       ( m1_subset_1 @ A @ C ) ))).
% 0.37/0.58  thf('34', plain,
% 0.37/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X11 @ X12)
% 0.37/0.58          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.37/0.58          | (m1_subset_1 @ X11 @ X13))),
% 0.37/0.58      inference('cnf', [status(esa)], [t4_subset])).
% 0.37/0.58  thf('35', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.58          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.58  thf('36', plain,
% 0.37/0.58      (((v1_xboole_0 @ sk_B_1)
% 0.37/0.58        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['32', '35'])).
% 0.37/0.58  thf('37', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('38', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('clc', [status(thm)], ['36', '37'])).
% 0.37/0.58  thf('39', plain,
% 0.37/0.58      (![X18 : $i, X19 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X18)
% 0.37/0.58          | ~ (m1_subset_1 @ X19 @ X18)
% 0.37/0.58          | (m1_subset_1 @ (k6_domain_1 @ X18 @ X19) @ (k1_zfmisc_1 @ X18)))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.37/0.58  thf('40', plain,
% 0.37/0.58      (((m1_subset_1 @ 
% 0.37/0.58         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.37/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.58  thf('41', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('clc', [status(thm)], ['36', '37'])).
% 0.37/0.58  thf('42', plain,
% 0.37/0.58      (![X20 : $i, X21 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X20)
% 0.37/0.58          | ~ (m1_subset_1 @ X21 @ X20)
% 0.37/0.58          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.37/0.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.37/0.58  thf('43', plain,
% 0.37/0.58      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.37/0.58          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.37/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.58  thf('44', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(cc1_subset_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( v1_xboole_0 @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.37/0.58  thf('45', plain,
% 0.37/0.58      (![X4 : $i, X5 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.37/0.58          | (v1_xboole_0 @ X4)
% 0.37/0.58          | ~ (v1_xboole_0 @ X5))),
% 0.37/0.58      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.37/0.58  thf('46', plain,
% 0.37/0.58      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.37/0.58  thf('47', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('48', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('clc', [status(thm)], ['46', '47'])).
% 0.37/0.58  thf('49', plain,
% 0.37/0.58      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.37/0.58         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.37/0.58      inference('clc', [status(thm)], ['43', '48'])).
% 0.37/0.58  thf('50', plain,
% 0.37/0.58      (((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ 
% 0.37/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['40', '49'])).
% 0.37/0.58  thf('51', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('clc', [status(thm)], ['46', '47'])).
% 0.37/0.58  thf('52', plain,
% 0.37/0.58      ((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ 
% 0.37/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('clc', [status(thm)], ['50', '51'])).
% 0.37/0.58  thf('53', plain,
% 0.37/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X11 @ X12)
% 0.37/0.58          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.37/0.58          | (m1_subset_1 @ X11 @ X13))),
% 0.37/0.58      inference('cnf', [status(esa)], [t4_subset])).
% 0.37/0.58  thf('54', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.58          | ~ (r2_hidden @ X0 @ (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.58  thf('55', plain,
% 0.37/0.58      (((v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))
% 0.37/0.58        | (m1_subset_1 @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))) @ 
% 0.37/0.58           (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['31', '54'])).
% 0.37/0.58  thf('56', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X3))),
% 0.37/0.58      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.37/0.58  thf('57', plain,
% 0.37/0.58      ((m1_subset_1 @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))) @ 
% 0.37/0.58        (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('clc', [status(thm)], ['55', '56'])).
% 0.37/0.58  thf('58', plain,
% 0.37/0.58      (![X20 : $i, X21 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X20)
% 0.37/0.58          | ~ (m1_subset_1 @ X21 @ X20)
% 0.37/0.58          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.37/0.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.37/0.58  thf('59', plain,
% 0.37/0.58      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58          (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))
% 0.37/0.58          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 0.37/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.58  thf('60', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('clc', [status(thm)], ['46', '47'])).
% 0.37/0.58  thf('61', plain,
% 0.37/0.58      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58         (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))
% 0.37/0.58         = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))),
% 0.37/0.58      inference('clc', [status(thm)], ['59', '60'])).
% 0.37/0.58  thf('62', plain,
% 0.37/0.58      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.37/0.58          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 0.37/0.58        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.37/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.58      inference('sup+', [status(thm)], ['30', '61'])).
% 0.37/0.58  thf('63', plain,
% 0.37/0.58      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.37/0.58         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.37/0.58      inference('clc', [status(thm)], ['43', '48'])).
% 0.37/0.58  thf('64', plain,
% 0.37/0.58      ((((k1_tarski @ (sk_B @ sk_B_1))
% 0.37/0.58          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 0.37/0.58        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.37/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['62', '63'])).
% 0.37/0.58  thf('65', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('66', plain,
% 0.37/0.58      ((~ (v1_zfmisc_1 @ sk_B_1)
% 0.37/0.58        | ((k1_tarski @ (sk_B @ sk_B_1))
% 0.37/0.58            = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))))),
% 0.37/0.58      inference('clc', [status(thm)], ['64', '65'])).
% 0.37/0.58  thf('67', plain,
% 0.37/0.58      ((((k1_tarski @ (sk_B @ sk_B_1))
% 0.37/0.58          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))))
% 0.37/0.58         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['29', '66'])).
% 0.37/0.58  thf('68', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X0)
% 0.37/0.58          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['20'])).
% 0.37/0.58  thf('69', plain,
% 0.37/0.58      ((((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ 
% 0.37/0.58          (k1_zfmisc_1 @ (k1_tarski @ (sk_B @ sk_B_1))))
% 0.37/0.58         | (v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 0.37/0.58         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['67', '68'])).
% 0.37/0.58  thf('70', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X3))),
% 0.37/0.58      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.37/0.58  thf('71', plain,
% 0.37/0.58      (((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ 
% 0.37/0.58         (k1_zfmisc_1 @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 0.37/0.58         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('clc', [status(thm)], ['69', '70'])).
% 0.37/0.58  thf('72', plain,
% 0.37/0.58      ((((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ (k1_zfmisc_1 @ sk_B_1))
% 0.37/0.58         | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.37/0.58         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['28', '71'])).
% 0.37/0.58  thf('73', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('split', [status(esa)], ['6'])).
% 0.37/0.58  thf('74', plain,
% 0.37/0.58      ((((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ (k1_zfmisc_1 @ sk_B_1))
% 0.37/0.58         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('demod', [status(thm)], ['72', '73'])).
% 0.37/0.58  thf('75', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('76', plain,
% 0.37/0.58      (((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ (k1_zfmisc_1 @ sk_B_1)))
% 0.37/0.58         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('clc', [status(thm)], ['74', '75'])).
% 0.37/0.58  thf('77', plain,
% 0.37/0.58      (![X8 : $i, X9 : $i]:
% 0.37/0.58         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.58  thf('78', plain,
% 0.37/0.58      (((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_B_1))
% 0.37/0.58         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['76', '77'])).
% 0.37/0.58  thf('79', plain,
% 0.37/0.58      (![X25 : $i, X26 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X25)
% 0.37/0.58          | ~ (v1_zfmisc_1 @ X25)
% 0.37/0.58          | ((X26) = (X25))
% 0.37/0.58          | ~ (r1_tarski @ X26 @ X25)
% 0.37/0.58          | (v1_xboole_0 @ X26))),
% 0.37/0.58      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.37/0.58  thf('80', plain,
% 0.37/0.58      ((((v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))
% 0.37/0.58         | ((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1))
% 0.37/0.58         | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.37/0.58         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['78', '79'])).
% 0.37/0.58  thf('81', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('split', [status(esa)], ['6'])).
% 0.37/0.58  thf('82', plain,
% 0.37/0.58      ((((v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))
% 0.37/0.58         | ((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1))
% 0.37/0.58         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('demod', [status(thm)], ['80', '81'])).
% 0.37/0.58  thf('83', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X3))),
% 0.37/0.58      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.37/0.58  thf('84', plain,
% 0.37/0.58      ((((v1_xboole_0 @ sk_B_1) | ((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1))))
% 0.37/0.58         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('clc', [status(thm)], ['82', '83'])).
% 0.37/0.58  thf('85', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('86', plain,
% 0.37/0.58      ((((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1)))
% 0.37/0.58         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('clc', [status(thm)], ['84', '85'])).
% 0.37/0.58  thf('87', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('clc', [status(thm)], ['36', '37'])).
% 0.37/0.58  thf(t36_tex_2, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.58           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.37/0.58  thf('88', plain,
% 0.37/0.58      (![X29 : $i, X30 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.37/0.58          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X30) @ X29) @ X30)
% 0.37/0.58          | ~ (l1_pre_topc @ X30)
% 0.37/0.58          | ~ (v2_pre_topc @ X30)
% 0.37/0.58          | (v2_struct_0 @ X30))),
% 0.37/0.58      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.37/0.58  thf('89', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.37/0.58           sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['87', '88'])).
% 0.37/0.58  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('92', plain,
% 0.37/0.58      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.37/0.58         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.37/0.58      inference('clc', [status(thm)], ['43', '48'])).
% 0.37/0.58  thf('93', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.37/0.58  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('95', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.37/0.58      inference('clc', [status(thm)], ['93', '94'])).
% 0.37/0.58  thf('96', plain,
% 0.37/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['86', '95'])).
% 0.37/0.58  thf('97', plain,
% 0.37/0.58      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('split', [status(esa)], ['8'])).
% 0.37/0.58  thf('98', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['96', '97'])).
% 0.37/0.58  thf('99', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.37/0.58      inference('split', [status(esa)], ['6'])).
% 0.37/0.58  thf('100', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('sat_resolution*', [status(thm)], ['9', '98', '99'])).
% 0.37/0.58  thf('101', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.37/0.58      inference('simpl_trail', [status(thm)], ['7', '100'])).
% 0.37/0.58  thf('102', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['5', '101'])).
% 0.37/0.58  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('104', plain,
% 0.37/0.58      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('clc', [status(thm)], ['102', '103'])).
% 0.37/0.58  thf('105', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('106', plain, (~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('clc', [status(thm)], ['104', '105'])).
% 0.37/0.58  thf('107', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('108', plain,
% 0.37/0.58      (![X27 : $i, X28 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X27)
% 0.37/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.37/0.58          | ~ (v2_tex_2 @ X27 @ X28)
% 0.37/0.58          | (m1_pre_topc @ (sk_C @ X27 @ X28) @ X28)
% 0.37/0.58          | ~ (l1_pre_topc @ X28)
% 0.37/0.58          | ~ (v2_pre_topc @ X28)
% 0.37/0.58          | (v2_struct_0 @ X28))),
% 0.37/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.37/0.58  thf('109', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.37/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['107', '108'])).
% 0.37/0.58  thf('110', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('112', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.37/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.37/0.58  thf('113', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.37/0.58      inference('simpl_trail', [status(thm)], ['7', '100'])).
% 0.37/0.58  thf('114', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.37/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['112', '113'])).
% 0.37/0.58  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('116', plain,
% 0.37/0.58      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.37/0.58      inference('clc', [status(thm)], ['114', '115'])).
% 0.37/0.58  thf('117', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('118', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.37/0.58      inference('clc', [status(thm)], ['116', '117'])).
% 0.37/0.58  thf(cc32_tex_2, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.37/0.58         ( l1_pre_topc @ A ) ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.58           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 0.37/0.58             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 0.37/0.58  thf('119', plain,
% 0.37/0.58      (![X23 : $i, X24 : $i]:
% 0.37/0.58         (~ (m1_pre_topc @ X23 @ X24)
% 0.37/0.58          | ~ (v1_tdlat_3 @ X23)
% 0.37/0.58          | (v7_struct_0 @ X23)
% 0.37/0.58          | (v2_struct_0 @ X23)
% 0.37/0.58          | ~ (l1_pre_topc @ X24)
% 0.37/0.58          | ~ (v2_tdlat_3 @ X24)
% 0.37/0.58          | ~ (v2_pre_topc @ X24)
% 0.37/0.58          | (v2_struct_0 @ X24))),
% 0.37/0.58      inference('cnf', [status(esa)], [cc32_tex_2])).
% 0.37/0.58  thf('120', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.58        | ~ (v2_tdlat_3 @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.58        | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.58        | ~ (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['118', '119'])).
% 0.37/0.58  thf('121', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('122', plain, ((v2_tdlat_3 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('124', plain,
% 0.37/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('split', [status(esa)], ['6'])).
% 0.37/0.58  thf('125', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('126', plain,
% 0.37/0.58      (![X27 : $i, X28 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X27)
% 0.37/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.37/0.58          | ~ (v2_tex_2 @ X27 @ X28)
% 0.37/0.58          | (v1_tdlat_3 @ (sk_C @ X27 @ X28))
% 0.37/0.58          | ~ (l1_pre_topc @ X28)
% 0.37/0.58          | ~ (v2_pre_topc @ X28)
% 0.37/0.58          | (v2_struct_0 @ X28))),
% 0.37/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.37/0.58  thf('127', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['125', '126'])).
% 0.37/0.58  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('130', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.37/0.58  thf('131', plain,
% 0.37/0.58      ((((v1_xboole_0 @ sk_B_1)
% 0.37/0.58         | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.58         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['124', '130'])).
% 0.37/0.58  thf('132', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('133', plain,
% 0.37/0.58      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.37/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('clc', [status(thm)], ['131', '132'])).
% 0.37/0.58  thf('134', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('135', plain,
% 0.37/0.58      (((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.37/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('clc', [status(thm)], ['133', '134'])).
% 0.37/0.58  thf('136', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('sat_resolution*', [status(thm)], ['9', '98', '99'])).
% 0.37/0.58  thf('137', plain, ((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('simpl_trail', [status(thm)], ['135', '136'])).
% 0.37/0.58  thf('138', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.58        | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['120', '121', '122', '123', '137'])).
% 0.37/0.58  thf('139', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('140', plain,
% 0.37/0.58      (((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.58        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('clc', [status(thm)], ['138', '139'])).
% 0.37/0.58  thf('141', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('142', plain,
% 0.37/0.58      (![X27 : $i, X28 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X27)
% 0.37/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.37/0.58          | ~ (v2_tex_2 @ X27 @ X28)
% 0.37/0.58          | ((X27) = (u1_struct_0 @ (sk_C @ X27 @ X28)))
% 0.37/0.58          | ~ (l1_pre_topc @ X28)
% 0.37/0.58          | ~ (v2_pre_topc @ X28)
% 0.37/0.58          | (v2_struct_0 @ X28))),
% 0.37/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.37/0.58  thf('143', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.37/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['141', '142'])).
% 0.37/0.58  thf('144', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('146', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.37/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.37/0.58  thf('147', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.37/0.58      inference('simpl_trail', [status(thm)], ['7', '100'])).
% 0.37/0.58  thf('148', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.37/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['146', '147'])).
% 0.37/0.58  thf('149', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('150', plain,
% 0.37/0.58      (((v1_xboole_0 @ sk_B_1)
% 0.37/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.37/0.58      inference('clc', [status(thm)], ['148', '149'])).
% 0.37/0.58  thf('151', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('152', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('clc', [status(thm)], ['150', '151'])).
% 0.37/0.58  thf(fc7_struct_0, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.58       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.37/0.58  thf('153', plain,
% 0.37/0.58      (![X17 : $i]:
% 0.37/0.58         ((v1_zfmisc_1 @ (u1_struct_0 @ X17))
% 0.37/0.58          | ~ (l1_struct_0 @ X17)
% 0.37/0.58          | ~ (v7_struct_0 @ X17))),
% 0.37/0.58      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.37/0.58  thf('154', plain,
% 0.37/0.58      (((v1_zfmisc_1 @ sk_B_1)
% 0.37/0.58        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.58        | ~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['152', '153'])).
% 0.37/0.58  thf('155', plain,
% 0.37/0.58      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.58      inference('split', [status(esa)], ['8'])).
% 0.37/0.58  thf('156', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.37/0.58      inference('sat_resolution*', [status(thm)], ['9', '98'])).
% 0.37/0.58  thf('157', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.37/0.58      inference('simpl_trail', [status(thm)], ['155', '156'])).
% 0.37/0.58  thf('158', plain,
% 0.37/0.58      ((~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.58        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('clc', [status(thm)], ['154', '157'])).
% 0.37/0.58  thf('159', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.37/0.58      inference('clc', [status(thm)], ['116', '117'])).
% 0.37/0.58  thf(dt_m1_pre_topc, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.37/0.58  thf('160', plain,
% 0.37/0.58      (![X15 : $i, X16 : $i]:
% 0.37/0.58         (~ (m1_pre_topc @ X15 @ X16)
% 0.37/0.58          | (l1_pre_topc @ X15)
% 0.37/0.58          | ~ (l1_pre_topc @ X16))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.37/0.58  thf('161', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['159', '160'])).
% 0.37/0.58  thf('162', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('163', plain, ((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['161', '162'])).
% 0.37/0.58  thf(dt_l1_pre_topc, axiom,
% 0.37/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.37/0.58  thf('164', plain,
% 0.37/0.58      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.58  thf('165', plain, ((l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['163', '164'])).
% 0.37/0.58  thf('166', plain, (~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['158', '165'])).
% 0.37/0.58  thf('167', plain, ((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('clc', [status(thm)], ['140', '166'])).
% 0.37/0.58  thf('168', plain, ($false), inference('demod', [status(thm)], ['106', '167'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
