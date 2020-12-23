%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ufvbiLk244

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 855 expanded)
%              Number of leaves         :   38 ( 259 expanded)
%              Depth                    :   26
%              Number of atoms          :  917 (8726 expanded)
%              Number of equality atoms :   15 (  64 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X8 ) @ X10 )
      | ~ ( r2_hidden @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_zfmisc_1 @ X25 )
      | ( X26 = X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('23',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X30 ) @ X29 ) @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('30',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['30','33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['12','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','40'])).

thf('42',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','43'])).

thf('45',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','44'])).

thf('46',plain,(
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

thf('47',plain,(
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

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('52',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('53',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','43','52'])).

thf('54',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['51','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['48','49','50','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('60',plain,(
    ! [X19: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ~ ( v7_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('61',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( m1_pre_topc @ ( sk_C_1 @ X27 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['51','53'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['70','71'])).

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

thf('73',plain,(
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

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X27 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['51','53'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X27 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['51','53'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['92','104'])).

thf('106',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['70','71'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('107',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('108',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['108','109'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('111',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('112',plain,(
    l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['61','105','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['45','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ufvbiLk244
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 190 iterations in 0.078s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.53  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.53  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.20/0.53  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(t44_tex_2, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.53         ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.53             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.53            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.53                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.20/0.53  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain, ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('3', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('4', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['3'])).
% 0.20/0.53  thf(d1_xboole_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.53  thf(l1_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X8 : $i, X10 : $i]:
% 0.20/0.53         ((r1_tarski @ (k1_tarski @ X8) @ X10) | ~ (r2_hidden @ X8 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf(t1_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.53           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X25 : $i, X26 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X25)
% 0.20/0.53          | ~ (v1_zfmisc_1 @ X25)
% 0.20/0.53          | ((X26) = (X25))
% 0.20/0.53          | ~ (r1_tarski @ X26 @ X25)
% 0.20/0.53          | (v1_xboole_0 @ X26))),
% 0.20/0.53      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X0)
% 0.20/0.53          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.20/0.53          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.20/0.53          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.53          | (v1_xboole_0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_zfmisc_1 @ X0)
% 0.20/0.53          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.20/0.53          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.20/0.53          | (v1_xboole_0 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.53  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.20/0.53  thf('11', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X0)
% 0.20/0.53          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.20/0.53          | ~ (v1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('16', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf(d3_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.53          | (r2_hidden @ X3 @ X5)
% 0.20/0.53          | ~ (r1_tarski @ X4 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.53        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '18'])).
% 0.20/0.53  thf('20', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('21', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf(t1_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.53  thf('23', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf(t36_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.20/0.53          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X30) @ X29) @ X30)
% 0.20/0.53          | ~ (l1_pre_topc @ X30)
% 0.20/0.53          | ~ (v2_pre_topc @ X30)
% 0.20/0.53          | (v2_struct_0 @ X30))),
% 0.20/0.53      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53           sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('28', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X20)
% 0.20/0.53          | ~ (m1_subset_1 @ X21 @ X20)
% 0.20/0.53          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.20/0.53          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.53  thf('33', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.20/0.53         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.20/0.53      inference('clc', [status(thm)], ['30', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['25', '26', '27', '34'])).
% 0.20/0.53  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('37', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.53        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['12', '37'])).
% 0.20/0.53  thf('39', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('40', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('43', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.53  thf('44', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['2', '43'])).
% 0.20/0.53  thf('45', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['1', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t34_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.53             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.53                ( ![C:$i]:
% 0.20/0.53                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.20/0.53                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.53                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X27)
% 0.20/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.53          | ~ (v2_tex_2 @ X27 @ X28)
% 0.20/0.53          | ((X27) = (u1_struct_0 @ (sk_C_1 @ X27 @ X28)))
% 0.20/0.53          | ~ (l1_pre_topc @ X28)
% 0.20/0.53          | ~ (v2_pre_topc @ X28)
% 0.20/0.53          | (v2_struct_0 @ X28))),
% 0.20/0.53      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.20/0.53        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['3'])).
% 0.20/0.53  thf('52', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.20/0.53      inference('split', [status(esa)], ['3'])).
% 0.20/0.53  thf('53', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['2', '43', '52'])).
% 0.20/0.53  thf('54', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['51', '53'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['48', '49', '50', '54'])).
% 0.20/0.53  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.53        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))),
% 0.20/0.53      inference('clc', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('58', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('59', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf(fc7_struct_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.53       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X19 : $i]:
% 0.20/0.53         ((v1_zfmisc_1 @ (u1_struct_0 @ X19))
% 0.20/0.53          | ~ (l1_struct_0 @ X19)
% 0.20/0.53          | ~ (v7_struct_0 @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (((v1_zfmisc_1 @ sk_B_1)
% 0.20/0.53        | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.53        | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['59', '60'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X27)
% 0.20/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.53          | ~ (v2_tex_2 @ X27 @ X28)
% 0.20/0.53          | (m1_pre_topc @ (sk_C_1 @ X27 @ X28) @ X28)
% 0.20/0.53          | ~ (l1_pre_topc @ X28)
% 0.20/0.53          | ~ (v2_pre_topc @ X28)
% 0.20/0.53          | (v2_struct_0 @ X28))),
% 0.20/0.53      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.53        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('67', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['51', '53'])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.20/0.53  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.53        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.53  thf('71', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('72', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['70', '71'])).
% 0.20/0.53  thf(cc32_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.53         ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 0.20/0.53             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (![X23 : $i, X24 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X23 @ X24)
% 0.20/0.53          | ~ (v1_tdlat_3 @ X23)
% 0.20/0.53          | (v7_struct_0 @ X23)
% 0.20/0.53          | (v2_struct_0 @ X23)
% 0.20/0.53          | ~ (l1_pre_topc @ X24)
% 0.20/0.53          | ~ (v2_tdlat_3 @ X24)
% 0.20/0.53          | ~ (v2_pre_topc @ X24)
% 0.20/0.53          | (v2_struct_0 @ X24))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc32_tex_2])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.53        | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.53        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('76', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X27)
% 0.20/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.53          | ~ (v2_tex_2 @ X27 @ X28)
% 0.20/0.53          | (v1_tdlat_3 @ (sk_C_1 @ X27 @ X28))
% 0.20/0.53          | ~ (l1_pre_topc @ X28)
% 0.20/0.53          | ~ (v2_pre_topc @ X28)
% 0.20/0.53          | (v2_struct_0 @ X28))),
% 0.20/0.53      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.53  thf('80', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.53        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.53  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.53        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.20/0.53  thf('84', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['51', '53'])).
% 0.20/0.53  thf('85', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['83', '84'])).
% 0.20/0.53  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_B_1) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['85', '86'])).
% 0.20/0.53  thf('88', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('89', plain, ((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['87', '88'])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.53        | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['74', '75', '76', '77', '89'])).
% 0.20/0.53  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('92', plain,
% 0.20/0.53      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.53        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['90', '91'])).
% 0.20/0.53  thf('93', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('94', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X27)
% 0.20/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.53          | ~ (v2_tex_2 @ X27 @ X28)
% 0.20/0.53          | ~ (v2_struct_0 @ (sk_C_1 @ X27 @ X28))
% 0.20/0.53          | ~ (l1_pre_topc @ X28)
% 0.20/0.53          | ~ (v2_pre_topc @ X28)
% 0.20/0.53          | (v2_struct_0 @ X28))),
% 0.20/0.53      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.53  thf('95', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.53        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.53  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('98', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.53        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.20/0.53  thf('99', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['51', '53'])).
% 0.20/0.53  thf('100', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['98', '99'])).
% 0.20/0.53  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('102', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['100', '101'])).
% 0.20/0.53  thf('103', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('104', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['102', '103'])).
% 0.20/0.53  thf('105', plain, ((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['92', '104'])).
% 0.20/0.53  thf('106', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['70', '71'])).
% 0.20/0.53  thf(dt_m1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.53  thf('107', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X17 @ X18)
% 0.20/0.53          | (l1_pre_topc @ X17)
% 0.20/0.53          | ~ (l1_pre_topc @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.53  thf('108', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.53  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('110', plain, ((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['108', '109'])).
% 0.20/0.53  thf(dt_l1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.53  thf('111', plain,
% 0.20/0.53      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.53  thf('112', plain, ((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['110', '111'])).
% 0.20/0.53  thf('113', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['61', '105', '112'])).
% 0.20/0.53  thf('114', plain, ($false), inference('demod', [status(thm)], ['45', '113'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
