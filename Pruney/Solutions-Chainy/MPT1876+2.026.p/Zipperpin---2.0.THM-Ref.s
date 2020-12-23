%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4D33WhRdwM

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  189 (1466 expanded)
%              Number of leaves         :   39 ( 415 expanded)
%              Depth                    :   29
%              Number of atoms          : 1212 (17721 expanded)
%              Number of equality atoms :   23 ( 178 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('5',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( sk_B @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( sk_B @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_zfmisc_1 @ X23 )
      | ( X24 = X23 )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X21 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( sk_B @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

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

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( X21
        = ( u1_struct_0 @ ( sk_C @ X21 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C @ X21 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('56',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X28 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X28 ) @ X27 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('65',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('68',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['65','70'])).

thf('72',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['62','71'])).

thf('73',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['19','72'])).

thf('74',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','75'])).

thf('77',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','78'])).

thf('80',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','79'])).

thf('81',plain,(
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

thf('82',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tex_2 @ X25 @ X26 )
      | ( X25
        = ( u1_struct_0 @ ( sk_C_1 @ X25 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('87',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('88',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','78','87'])).

thf('89',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['86','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['83','84','85','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('95',plain,(
    ! [X10: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ~ ( v7_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('96',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tex_2 @ X25 @ X26 )
      | ( m1_pre_topc @ ( sk_C_1 @ X25 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['86','88'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['105','106'])).

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

thf('108',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( v1_tdlat_3 @ X19 )
      | ( v7_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_tdlat_3 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc32_tex_2])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tex_2 @ X25 @ X26 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X25 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['86','88'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tex_2 @ X25 @ X26 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X25 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['86','88'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['126','138'])).

thf('140',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['105','106'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('141',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('142',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['142','143'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('145',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('146',plain,(
    l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['96','139','146'])).

thf('148',plain,(
    $false ),
    inference(demod,[status(thm)],['80','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4D33WhRdwM
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 171 iterations in 0.122s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.58  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.58  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.58  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.20/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.58  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.58  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.20/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.58  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.58  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.58  thf(t44_tex_2, conjecture,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.58         ( l1_pre_topc @ A ) ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.58           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i]:
% 0.20/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.58            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.58          ( ![B:$i]:
% 0.20/0.58            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.58                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.58              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.20/0.58  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain, ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('3', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('4', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.58      inference('split', [status(esa)], ['3'])).
% 0.20/0.58  thf(existence_m1_subset_1, axiom,
% 0.20/0.58    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.20/0.58  thf('5', plain, (![X1 : $i]: (m1_subset_1 @ (sk_B @ X1) @ X1)),
% 0.20/0.58      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.20/0.58  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.58       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (![X16 : $i, X17 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X16)
% 0.20/0.58          | ~ (m1_subset_1 @ X17 @ X16)
% 0.20/0.58          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.58          | (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.58  thf('8', plain, (![X1 : $i]: (m1_subset_1 @ (sk_B @ X1) @ X1)),
% 0.20/0.58      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.20/0.58  thf(dt_k6_domain_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.58       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.58  thf('9', plain,
% 0.20/0.58      (![X14 : $i, X15 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X14)
% 0.20/0.58          | ~ (m1_subset_1 @ X15 @ X14)
% 0.20/0.58          | (m1_subset_1 @ (k6_domain_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14)))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.58  thf('10', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.20/0.58          | (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.58  thf(t3_subset, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (![X4 : $i, X5 : $i]:
% 0.20/0.58         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X0)
% 0.20/0.58          | (r1_tarski @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0)
% 0.20/0.58          | (v1_xboole_0 @ X0)
% 0.20/0.58          | (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['7', '12'])).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.58  thf(t1_tex_2, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.58           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      (![X23 : $i, X24 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X23)
% 0.20/0.58          | ~ (v1_zfmisc_1 @ X23)
% 0.20/0.58          | ((X24) = (X23))
% 0.20/0.58          | ~ (r1_tarski @ X24 @ X23)
% 0.20/0.58          | (v1_xboole_0 @ X24))),
% 0.20/0.58      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X0)
% 0.20/0.58          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.20/0.58          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.20/0.58          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.58          | (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_zfmisc_1 @ X0)
% 0.20/0.58          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.20/0.58          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.20/0.58          | (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.58  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.20/0.58  thf('18', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.20/0.58      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.20/0.58  thf('19', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X0)
% 0.20/0.58          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.20/0.58          | ~ (v1_zfmisc_1 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(t10_tsep_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.58           ( ?[C:$i]:
% 0.20/0.58             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.20/0.58               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.20/0.58  thf('21', plain,
% 0.20/0.58      (![X21 : $i, X22 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X21)
% 0.20/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.20/0.58          | (m1_pre_topc @ (sk_C @ X21 @ X22) @ X22)
% 0.20/0.58          | ~ (l1_pre_topc @ X22)
% 0.20/0.58          | (v2_struct_0 @ X22))),
% 0.20/0.58      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.58  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.58  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.20/0.58      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.58  thf('27', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('28', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.58      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.58  thf('29', plain, (![X1 : $i]: (m1_subset_1 @ (sk_B @ X1) @ X1)),
% 0.20/0.58      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.20/0.58  thf(t55_pre_topc, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.58           ( ![C:$i]:
% 0.20/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.58               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.58         ((v2_struct_0 @ X11)
% 0.20/0.58          | ~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.58          | (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.20/0.58          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.20/0.58          | ~ (l1_pre_topc @ X12)
% 0.20/0.58          | (v2_struct_0 @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((v2_struct_0 @ X1)
% 0.20/0.58          | ~ (l1_pre_topc @ X1)
% 0.20/0.58          | (m1_subset_1 @ (sk_B @ (u1_struct_0 @ X0)) @ (u1_struct_0 @ X1))
% 0.20/0.58          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.58          | (v2_struct_0 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      (((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.58        | (m1_subset_1 @ (sk_B @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.20/0.58           (u1_struct_0 @ sk_A))
% 0.20/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58        | (v2_struct_0 @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['28', '31'])).
% 0.20/0.58  thf('33', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (![X21 : $i, X22 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X21)
% 0.20/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.20/0.58          | ((X21) = (u1_struct_0 @ (sk_C @ X21 @ X22)))
% 0.20/0.58          | ~ (l1_pre_topc @ X22)
% 0.20/0.58          | (v2_struct_0 @ X22))),
% 0.20/0.58      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.58  thf('35', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.58  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('37', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.58  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('39', plain,
% 0.20/0.58      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.20/0.58      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.58  thf('40', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('41', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.20/0.58      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.58  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('43', plain,
% 0.20/0.58      (((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.58        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.20/0.58        | (v2_struct_0 @ sk_A))),
% 0.20/0.58      inference('demod', [status(thm)], ['32', '41', '42'])).
% 0.20/0.58  thf('44', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('45', plain,
% 0.20/0.58      (![X21 : $i, X22 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X21)
% 0.20/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.20/0.58          | ~ (v2_struct_0 @ (sk_C @ X21 @ X22))
% 0.20/0.58          | ~ (l1_pre_topc @ X22)
% 0.20/0.58          | (v2_struct_0 @ X22))),
% 0.20/0.58      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.58  thf('46', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.58  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('48', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.58  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('50', plain,
% 0.20/0.58      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.20/0.58      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.58  thf('51', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('52', plain, (~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.20/0.58      inference('clc', [status(thm)], ['50', '51'])).
% 0.20/0.58  thf('53', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.58      inference('clc', [status(thm)], ['43', '52'])).
% 0.20/0.58  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('55', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.58      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.58  thf(t36_tex_2, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.58           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.20/0.58  thf('56', plain,
% 0.20/0.58      (![X27 : $i, X28 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 0.20/0.58          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X28) @ X27) @ X28)
% 0.20/0.58          | ~ (l1_pre_topc @ X28)
% 0.20/0.58          | ~ (v2_pre_topc @ X28)
% 0.20/0.58          | (v2_struct_0 @ X28))),
% 0.20/0.58      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.20/0.58  thf('57', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.58           sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.58  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('60', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.58           sk_A))),
% 0.20/0.58      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.20/0.58  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('62', plain,
% 0.20/0.58      ((v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.58        sk_A)),
% 0.20/0.58      inference('clc', [status(thm)], ['60', '61'])).
% 0.20/0.58  thf('63', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.58      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.58  thf('64', plain,
% 0.20/0.58      (![X16 : $i, X17 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X16)
% 0.20/0.58          | ~ (m1_subset_1 @ X17 @ X16)
% 0.20/0.58          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.58  thf('65', plain,
% 0.20/0.58      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.20/0.58          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.20/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.58  thf('66', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(cc1_subset_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.20/0.58  thf('67', plain,
% 0.20/0.58      (![X2 : $i, X3 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.20/0.58          | (v1_xboole_0 @ X2)
% 0.20/0.58          | ~ (v1_xboole_0 @ X3))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.58  thf('68', plain,
% 0.20/0.58      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.58  thf('69', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('70', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.58      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.58  thf('71', plain,
% 0.20/0.58      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.20/0.58         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.20/0.58      inference('clc', [status(thm)], ['65', '70'])).
% 0.20/0.58  thf('72', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.20/0.58      inference('demod', [status(thm)], ['62', '71'])).
% 0.20/0.58  thf('73', plain,
% 0.20/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.58        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('sup+', [status(thm)], ['19', '72'])).
% 0.20/0.58  thf('74', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('75', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.58      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.58  thf('76', plain,
% 0.20/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['4', '75'])).
% 0.20/0.58  thf('77', plain,
% 0.20/0.58      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('78', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.58  thf('79', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['2', '78'])).
% 0.20/0.58  thf('80', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['1', '79'])).
% 0.20/0.58  thf('81', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(t34_tex_2, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.58           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.58                ( ![C:$i]:
% 0.20/0.58                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.20/0.58                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.58                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.58  thf('82', plain,
% 0.20/0.58      (![X25 : $i, X26 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X25)
% 0.20/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.58          | ~ (v2_tex_2 @ X25 @ X26)
% 0.20/0.58          | ((X25) = (u1_struct_0 @ (sk_C_1 @ X25 @ X26)))
% 0.20/0.58          | ~ (l1_pre_topc @ X26)
% 0.20/0.58          | ~ (v2_pre_topc @ X26)
% 0.20/0.58          | (v2_struct_0 @ X26))),
% 0.20/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.58  thf('83', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.20/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.58  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('86', plain,
% 0.20/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.58      inference('split', [status(esa)], ['3'])).
% 0.20/0.58  thf('87', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.20/0.58      inference('split', [status(esa)], ['3'])).
% 0.20/0.58  thf('88', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['2', '78', '87'])).
% 0.20/0.58  thf('89', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['86', '88'])).
% 0.20/0.58  thf('90', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('demod', [status(thm)], ['83', '84', '85', '89'])).
% 0.20/0.58  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('92', plain,
% 0.20/0.58      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))),
% 0.20/0.58      inference('clc', [status(thm)], ['90', '91'])).
% 0.20/0.58  thf('93', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('94', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.58      inference('clc', [status(thm)], ['92', '93'])).
% 0.20/0.58  thf(fc7_struct_0, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.58       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.58  thf('95', plain,
% 0.20/0.58      (![X10 : $i]:
% 0.20/0.58         ((v1_zfmisc_1 @ (u1_struct_0 @ X10))
% 0.20/0.58          | ~ (l1_struct_0 @ X10)
% 0.20/0.58          | ~ (v7_struct_0 @ X10))),
% 0.20/0.58      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.20/0.58  thf('96', plain,
% 0.20/0.58      (((v1_zfmisc_1 @ sk_B_1)
% 0.20/0.58        | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.58        | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['94', '95'])).
% 0.20/0.58  thf('97', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('98', plain,
% 0.20/0.58      (![X25 : $i, X26 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X25)
% 0.20/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.58          | ~ (v2_tex_2 @ X25 @ X26)
% 0.20/0.58          | (m1_pre_topc @ (sk_C_1 @ X25 @ X26) @ X26)
% 0.20/0.58          | ~ (l1_pre_topc @ X26)
% 0.20/0.58          | ~ (v2_pre_topc @ X26)
% 0.20/0.58          | (v2_struct_0 @ X26))),
% 0.20/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.58  thf('99', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['97', '98'])).
% 0.20/0.58  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('102', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['86', '88'])).
% 0.20/0.58  thf('103', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 0.20/0.58  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('105', plain,
% 0.20/0.58      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.58        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))),
% 0.20/0.58      inference('clc', [status(thm)], ['103', '104'])).
% 0.20/0.58  thf('106', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('107', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.58      inference('clc', [status(thm)], ['105', '106'])).
% 0.20/0.58  thf(cc32_tex_2, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.58         ( l1_pre_topc @ A ) ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.58           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 0.20/0.58             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 0.20/0.58  thf('108', plain,
% 0.20/0.58      (![X19 : $i, X20 : $i]:
% 0.20/0.58         (~ (m1_pre_topc @ X19 @ X20)
% 0.20/0.58          | ~ (v1_tdlat_3 @ X19)
% 0.20/0.58          | (v7_struct_0 @ X19)
% 0.20/0.58          | (v2_struct_0 @ X19)
% 0.20/0.58          | ~ (l1_pre_topc @ X20)
% 0.20/0.58          | ~ (v2_tdlat_3 @ X20)
% 0.20/0.58          | ~ (v2_pre_topc @ X20)
% 0.20/0.58          | (v2_struct_0 @ X20))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc32_tex_2])).
% 0.20/0.58  thf('109', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.58        | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.58        | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.58        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['107', '108'])).
% 0.20/0.58  thf('110', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('111', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('113', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('114', plain,
% 0.20/0.58      (![X25 : $i, X26 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X25)
% 0.20/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.58          | ~ (v2_tex_2 @ X25 @ X26)
% 0.20/0.58          | (v1_tdlat_3 @ (sk_C_1 @ X25 @ X26))
% 0.20/0.58          | ~ (l1_pre_topc @ X26)
% 0.20/0.58          | ~ (v2_pre_topc @ X26)
% 0.20/0.58          | (v2_struct_0 @ X26))),
% 0.20/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.58  thf('115', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['113', '114'])).
% 0.20/0.58  thf('116', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('118', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['86', '88'])).
% 0.20/0.58  thf('119', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 0.20/0.58  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('121', plain,
% 0.20/0.58      (((v1_xboole_0 @ sk_B_1) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.58      inference('clc', [status(thm)], ['119', '120'])).
% 0.20/0.58  thf('122', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('123', plain, ((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.58      inference('clc', [status(thm)], ['121', '122'])).
% 0.20/0.58  thf('124', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.58        | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.58      inference('demod', [status(thm)], ['109', '110', '111', '112', '123'])).
% 0.20/0.58  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('126', plain,
% 0.20/0.58      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.58        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.58      inference('clc', [status(thm)], ['124', '125'])).
% 0.20/0.58  thf('127', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('128', plain,
% 0.20/0.58      (![X25 : $i, X26 : $i]:
% 0.20/0.58         ((v1_xboole_0 @ X25)
% 0.20/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.58          | ~ (v2_tex_2 @ X25 @ X26)
% 0.20/0.58          | ~ (v2_struct_0 @ (sk_C_1 @ X25 @ X26))
% 0.20/0.58          | ~ (l1_pre_topc @ X26)
% 0.20/0.58          | ~ (v2_pre_topc @ X26)
% 0.20/0.58          | (v2_struct_0 @ X26))),
% 0.20/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.58  thf('129', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['127', '128'])).
% 0.20/0.58  thf('130', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('132', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.20/0.58  thf('133', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['86', '88'])).
% 0.20/0.58  thf('134', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.58      inference('demod', [status(thm)], ['132', '133'])).
% 0.20/0.58  thf('135', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('136', plain,
% 0.20/0.58      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.58      inference('clc', [status(thm)], ['134', '135'])).
% 0.20/0.58  thf('137', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('138', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.58      inference('clc', [status(thm)], ['136', '137'])).
% 0.20/0.58  thf('139', plain, ((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.58      inference('clc', [status(thm)], ['126', '138'])).
% 0.20/0.58  thf('140', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.58      inference('clc', [status(thm)], ['105', '106'])).
% 0.20/0.58  thf(dt_m1_pre_topc, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_pre_topc @ A ) =>
% 0.20/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.58  thf('141', plain,
% 0.20/0.58      (![X8 : $i, X9 : $i]:
% 0.20/0.58         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.58  thf('142', plain,
% 0.20/0.58      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['140', '141'])).
% 0.20/0.58  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('144', plain, ((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.58      inference('demod', [status(thm)], ['142', '143'])).
% 0.20/0.58  thf(dt_l1_pre_topc, axiom,
% 0.20/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.58  thf('145', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.58  thf('146', plain, ((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['144', '145'])).
% 0.20/0.58  thf('147', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.20/0.58      inference('demod', [status(thm)], ['96', '139', '146'])).
% 0.20/0.58  thf('148', plain, ($false), inference('demod', [status(thm)], ['80', '147'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
