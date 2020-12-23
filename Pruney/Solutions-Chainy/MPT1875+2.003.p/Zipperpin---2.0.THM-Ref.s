%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PUr4Ne54UG

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:51 EST 2020

% Result     : Theorem 6.13s
% Output     : Refutation 6.13s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 500 expanded)
%              Number of leaves         :   47 ( 163 expanded)
%              Depth                    :   25
%              Number of atoms          : 1284 (5019 expanded)
%              Number of equality atoms :   55 ( 100 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t43_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X27 @ X26 ) )
        = X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X25: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ~ ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('9',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( l1_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('16',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('21',plain,(
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

thf('22',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X41 ) @ X42 )
      | ~ ( v1_tdlat_3 @ X41 )
      | ~ ( m1_pre_topc @ X41 @ X42 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf(cc5_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_borsuk_1 @ B @ A )
            & ( v1_tsep_1 @ B @ A )
            & ( v1_tdlat_3 @ B ) ) ) ) )).

thf('25',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ( v1_tdlat_3 @ X33 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v1_tdlat_3 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['2','3'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      | ( v2_tex_2 @ sk_B_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','32','33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['18','42'])).

thf('44',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['2','3'])).

thf('45',plain,(
    ! [X25: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ~ ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('50',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('52',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['43','52'])).

thf('54',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['2','3'])).

thf('55',plain,(
    ! [X25: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ~ ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('57',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('58',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( u1_struct_0 @ X0 )
        = ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('67',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d6_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( r1_tarski @ ( sk_C @ X35 @ X36 ) @ X35 )
      | ( v2_tex_2 @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('74',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('75',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('77',plain,(
    ! [X35: $i,X36: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v4_pre_topc @ X38 @ X36 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 @ X38 )
       != ( sk_C @ X35 @ X36 ) )
      | ( v2_tex_2 @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('80',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X6 @ X8 @ X7 )
        = ( k9_subset_1 @ X6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('83',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('85',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('86',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['78','95'])).

thf('97',plain,
    ( ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['75','96'])).

thf('98',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('99',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ( v4_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('104',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('105',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('106',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_tdlat_3 @ X39 )
      | ( v3_pre_topc @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('107',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['102','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['97','112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(eq_fact,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_tex_2 @ ( k3_xboole_0 @ X1 @ X0 ) @ sk_A )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['64','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ ( k3_xboole_0 @ X1 @ X0 ) @ sk_A )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(condensation,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i,X2: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ sk_A )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['63','123'])).

thf('125',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
      | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['54','125'])).

thf('127',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('132',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    $false ),
    inference('sup-',[status(thm)],['53','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PUr4Ne54UG
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:01:26 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 6.13/6.33  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.13/6.33  % Solved by: fo/fo7.sh
% 6.13/6.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.13/6.33  % done 6355 iterations in 5.858s
% 6.13/6.33  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.13/6.33  % SZS output start Refutation
% 6.13/6.33  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.13/6.33  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 6.13/6.33  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.13/6.33  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 6.13/6.33  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.13/6.33  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 6.13/6.33  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.13/6.33  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 6.13/6.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.13/6.33  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.13/6.33  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 6.13/6.33  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 6.13/6.33  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 6.13/6.33  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.13/6.33  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 6.13/6.33  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.13/6.33  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 6.13/6.33  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.13/6.33  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.13/6.33  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.13/6.33  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 6.13/6.33  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 6.13/6.33  thf(sk_A_type, type, sk_A: $i).
% 6.13/6.33  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 6.13/6.33  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 6.13/6.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.13/6.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.13/6.33  thf(t43_tex_2, conjecture,
% 6.13/6.33    (![A:$i]:
% 6.13/6.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 6.13/6.33         ( l1_pre_topc @ A ) ) =>
% 6.13/6.33       ( ![B:$i]:
% 6.13/6.33         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.13/6.33           ( v2_tex_2 @ B @ A ) ) ) ))).
% 6.13/6.33  thf(zf_stmt_0, negated_conjecture,
% 6.13/6.33    (~( ![A:$i]:
% 6.13/6.33        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.13/6.33            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.13/6.33          ( ![B:$i]:
% 6.13/6.33            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.13/6.33              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 6.13/6.33    inference('cnf.neg', [status(esa)], [t43_tex_2])).
% 6.13/6.33  thf('0', plain,
% 6.13/6.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf(t29_pre_topc, axiom,
% 6.13/6.33    (![A:$i]:
% 6.13/6.33     ( ( l1_pre_topc @ A ) =>
% 6.13/6.33       ( ![B:$i]:
% 6.13/6.33         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.13/6.33           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 6.13/6.33  thf('1', plain,
% 6.13/6.33      (![X26 : $i, X27 : $i]:
% 6.13/6.33         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 6.13/6.33          | ((u1_struct_0 @ (k1_pre_topc @ X27 @ X26)) = (X26))
% 6.13/6.33          | ~ (l1_pre_topc @ X27))),
% 6.13/6.33      inference('cnf', [status(esa)], [t29_pre_topc])).
% 6.13/6.33  thf('2', plain,
% 6.13/6.33      ((~ (l1_pre_topc @ sk_A)
% 6.13/6.33        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1)))),
% 6.13/6.33      inference('sup-', [status(thm)], ['0', '1'])).
% 6.13/6.33  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('4', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 6.13/6.33      inference('demod', [status(thm)], ['2', '3'])).
% 6.13/6.33  thf(fc1_struct_0, axiom,
% 6.13/6.33    (![A:$i]:
% 6.13/6.33     ( ( ( v2_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 6.13/6.33       ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ))).
% 6.13/6.33  thf('5', plain,
% 6.13/6.33      (![X25 : $i]:
% 6.13/6.33         ((v1_xboole_0 @ (u1_struct_0 @ X25))
% 6.13/6.33          | ~ (l1_struct_0 @ X25)
% 6.13/6.33          | ~ (v2_struct_0 @ X25))),
% 6.13/6.33      inference('cnf', [status(esa)], [fc1_struct_0])).
% 6.13/6.33  thf('6', plain,
% 6.13/6.33      (((v1_xboole_0 @ sk_B_1)
% 6.13/6.33        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))
% 6.13/6.33        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 6.13/6.33      inference('sup+', [status(thm)], ['4', '5'])).
% 6.13/6.33  thf('7', plain,
% 6.13/6.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf(dt_k1_pre_topc, axiom,
% 6.13/6.33    (![A:$i,B:$i]:
% 6.13/6.33     ( ( ( l1_pre_topc @ A ) & 
% 6.13/6.33         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.13/6.33       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 6.13/6.33         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 6.13/6.33  thf('8', plain,
% 6.13/6.33      (![X20 : $i, X21 : $i]:
% 6.13/6.33         (~ (l1_pre_topc @ X20)
% 6.13/6.33          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 6.13/6.33          | (m1_pre_topc @ (k1_pre_topc @ X20 @ X21) @ X20))),
% 6.13/6.33      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 6.13/6.33  thf('9', plain,
% 6.13/6.33      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)
% 6.13/6.33        | ~ (l1_pre_topc @ sk_A))),
% 6.13/6.33      inference('sup-', [status(thm)], ['7', '8'])).
% 6.13/6.33  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('11', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)),
% 6.13/6.33      inference('demod', [status(thm)], ['9', '10'])).
% 6.13/6.33  thf(dt_m1_pre_topc, axiom,
% 6.13/6.33    (![A:$i]:
% 6.13/6.33     ( ( l1_pre_topc @ A ) =>
% 6.13/6.33       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 6.13/6.33  thf('12', plain,
% 6.13/6.33      (![X23 : $i, X24 : $i]:
% 6.13/6.33         (~ (m1_pre_topc @ X23 @ X24)
% 6.13/6.33          | (l1_pre_topc @ X23)
% 6.13/6.33          | ~ (l1_pre_topc @ X24))),
% 6.13/6.33      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 6.13/6.33  thf('13', plain,
% 6.13/6.33      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 6.13/6.33      inference('sup-', [status(thm)], ['11', '12'])).
% 6.13/6.33  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('15', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1))),
% 6.13/6.33      inference('demod', [status(thm)], ['13', '14'])).
% 6.13/6.33  thf(dt_l1_pre_topc, axiom,
% 6.13/6.33    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 6.13/6.33  thf('16', plain,
% 6.13/6.33      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 6.13/6.33      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 6.13/6.33  thf('17', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))),
% 6.13/6.33      inference('sup-', [status(thm)], ['15', '16'])).
% 6.13/6.33  thf('18', plain,
% 6.13/6.33      (((v1_xboole_0 @ sk_B_1)
% 6.13/6.33        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 6.13/6.33      inference('demod', [status(thm)], ['6', '17'])).
% 6.13/6.33  thf('19', plain,
% 6.13/6.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('20', plain,
% 6.13/6.33      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 6.13/6.33      inference('demod', [status(thm)], ['2', '3'])).
% 6.13/6.33  thf(t26_tex_2, axiom,
% 6.13/6.33    (![A:$i]:
% 6.13/6.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 6.13/6.33       ( ![B:$i]:
% 6.13/6.33         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 6.13/6.33           ( ![C:$i]:
% 6.13/6.33             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.13/6.33               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 6.13/6.33                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 6.13/6.33  thf('21', plain,
% 6.13/6.33      (![X41 : $i, X42 : $i, X43 : $i]:
% 6.13/6.33         ((v2_struct_0 @ X41)
% 6.13/6.33          | ~ (m1_pre_topc @ X41 @ X42)
% 6.13/6.33          | ((X43) != (u1_struct_0 @ X41))
% 6.13/6.33          | ~ (v1_tdlat_3 @ X41)
% 6.13/6.33          | (v2_tex_2 @ X43 @ X42)
% 6.13/6.33          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 6.13/6.33          | ~ (l1_pre_topc @ X42)
% 6.13/6.33          | (v2_struct_0 @ X42))),
% 6.13/6.33      inference('cnf', [status(esa)], [t26_tex_2])).
% 6.13/6.33  thf('22', plain,
% 6.13/6.33      (![X41 : $i, X42 : $i]:
% 6.13/6.33         ((v2_struct_0 @ X42)
% 6.13/6.33          | ~ (l1_pre_topc @ X42)
% 6.13/6.33          | ~ (m1_subset_1 @ (u1_struct_0 @ X41) @ 
% 6.13/6.33               (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 6.13/6.33          | (v2_tex_2 @ (u1_struct_0 @ X41) @ X42)
% 6.13/6.33          | ~ (v1_tdlat_3 @ X41)
% 6.13/6.33          | ~ (m1_pre_topc @ X41 @ X42)
% 6.13/6.33          | (v2_struct_0 @ X41))),
% 6.13/6.33      inference('simplify', [status(thm)], ['21'])).
% 6.13/6.33  thf('23', plain,
% 6.13/6.33      (![X0 : $i]:
% 6.13/6.33         (~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 6.13/6.33          | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))
% 6.13/6.33          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ X0)
% 6.13/6.33          | ~ (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B_1))
% 6.13/6.33          | (v2_tex_2 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) @ X0)
% 6.13/6.33          | ~ (l1_pre_topc @ X0)
% 6.13/6.33          | (v2_struct_0 @ X0))),
% 6.13/6.33      inference('sup-', [status(thm)], ['20', '22'])).
% 6.13/6.33  thf('24', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)),
% 6.13/6.33      inference('demod', [status(thm)], ['9', '10'])).
% 6.13/6.33  thf(cc5_tdlat_3, axiom,
% 6.13/6.33    (![A:$i]:
% 6.13/6.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 6.13/6.33         ( l1_pre_topc @ A ) ) =>
% 6.13/6.33       ( ![B:$i]:
% 6.13/6.33         ( ( m1_pre_topc @ B @ A ) =>
% 6.13/6.33           ( ( v1_borsuk_1 @ B @ A ) & ( v1_tsep_1 @ B @ A ) & 
% 6.13/6.33             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 6.13/6.33  thf('25', plain,
% 6.13/6.33      (![X33 : $i, X34 : $i]:
% 6.13/6.33         (~ (m1_pre_topc @ X33 @ X34)
% 6.13/6.33          | (v1_tdlat_3 @ X33)
% 6.13/6.33          | ~ (l1_pre_topc @ X34)
% 6.13/6.33          | ~ (v1_tdlat_3 @ X34)
% 6.13/6.33          | ~ (v2_pre_topc @ X34)
% 6.13/6.33          | (v2_struct_0 @ X34))),
% 6.13/6.33      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 6.13/6.33  thf('26', plain,
% 6.13/6.33      (((v2_struct_0 @ sk_A)
% 6.13/6.33        | ~ (v2_pre_topc @ sk_A)
% 6.13/6.33        | ~ (v1_tdlat_3 @ sk_A)
% 6.13/6.33        | ~ (l1_pre_topc @ sk_A)
% 6.13/6.33        | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 6.13/6.33      inference('sup-', [status(thm)], ['24', '25'])).
% 6.13/6.33  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('28', plain, ((v1_tdlat_3 @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('30', plain,
% 6.13/6.33      (((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 6.13/6.33      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 6.13/6.33  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('32', plain, ((v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B_1))),
% 6.13/6.33      inference('clc', [status(thm)], ['30', '31'])).
% 6.13/6.33  thf('33', plain,
% 6.13/6.33      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 6.13/6.33      inference('demod', [status(thm)], ['2', '3'])).
% 6.13/6.33  thf('34', plain,
% 6.13/6.33      (![X0 : $i]:
% 6.13/6.33         (~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 6.13/6.33          | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))
% 6.13/6.33          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ X0)
% 6.13/6.33          | (v2_tex_2 @ sk_B_1 @ X0)
% 6.13/6.33          | ~ (l1_pre_topc @ X0)
% 6.13/6.33          | (v2_struct_0 @ X0))),
% 6.13/6.33      inference('demod', [status(thm)], ['23', '32', '33'])).
% 6.13/6.33  thf('35', plain,
% 6.13/6.33      (((v2_struct_0 @ sk_A)
% 6.13/6.33        | ~ (l1_pre_topc @ sk_A)
% 6.13/6.33        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 6.13/6.33        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)
% 6.13/6.33        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 6.13/6.33      inference('sup-', [status(thm)], ['19', '34'])).
% 6.13/6.33  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('37', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)),
% 6.13/6.33      inference('demod', [status(thm)], ['9', '10'])).
% 6.13/6.33  thf('38', plain,
% 6.13/6.33      (((v2_struct_0 @ sk_A)
% 6.13/6.33        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 6.13/6.33        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 6.13/6.33      inference('demod', [status(thm)], ['35', '36', '37'])).
% 6.13/6.33  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('40', plain,
% 6.13/6.33      (((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))
% 6.13/6.33        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 6.13/6.33      inference('clc', [status(thm)], ['38', '39'])).
% 6.13/6.33  thf('41', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('42', plain, ((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))),
% 6.13/6.33      inference('clc', [status(thm)], ['40', '41'])).
% 6.13/6.33  thf('43', plain, ((v1_xboole_0 @ sk_B_1)),
% 6.13/6.33      inference('demod', [status(thm)], ['18', '42'])).
% 6.13/6.33  thf('44', plain,
% 6.13/6.33      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 6.13/6.33      inference('demod', [status(thm)], ['2', '3'])).
% 6.13/6.33  thf('45', plain,
% 6.13/6.33      (![X25 : $i]:
% 6.13/6.33         ((v1_xboole_0 @ (u1_struct_0 @ X25))
% 6.13/6.33          | ~ (l1_struct_0 @ X25)
% 6.13/6.33          | ~ (v2_struct_0 @ X25))),
% 6.13/6.33      inference('cnf', [status(esa)], [fc1_struct_0])).
% 6.13/6.33  thf(l13_xboole_0, axiom,
% 6.13/6.33    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.13/6.33  thf('46', plain,
% 6.13/6.33      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.13/6.33      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.13/6.33  thf('47', plain,
% 6.13/6.33      (![X0 : $i]:
% 6.13/6.33         (~ (v2_struct_0 @ X0)
% 6.13/6.33          | ~ (l1_struct_0 @ X0)
% 6.13/6.33          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 6.13/6.33      inference('sup-', [status(thm)], ['45', '46'])).
% 6.13/6.33  thf('48', plain,
% 6.13/6.33      ((((sk_B_1) = (k1_xboole_0))
% 6.13/6.33        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))
% 6.13/6.33        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 6.13/6.33      inference('sup+', [status(thm)], ['44', '47'])).
% 6.13/6.33  thf('49', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))),
% 6.13/6.33      inference('sup-', [status(thm)], ['15', '16'])).
% 6.13/6.33  thf('50', plain,
% 6.13/6.33      ((((sk_B_1) = (k1_xboole_0))
% 6.13/6.33        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 6.13/6.33      inference('demod', [status(thm)], ['48', '49'])).
% 6.13/6.33  thf('51', plain, ((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))),
% 6.13/6.33      inference('clc', [status(thm)], ['40', '41'])).
% 6.13/6.33  thf('52', plain, (((sk_B_1) = (k1_xboole_0))),
% 6.13/6.33      inference('demod', [status(thm)], ['50', '51'])).
% 6.13/6.33  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.13/6.33      inference('demod', [status(thm)], ['43', '52'])).
% 6.13/6.33  thf('54', plain,
% 6.13/6.33      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 6.13/6.33      inference('demod', [status(thm)], ['2', '3'])).
% 6.13/6.33  thf('55', plain,
% 6.13/6.33      (![X25 : $i]:
% 6.13/6.33         ((v1_xboole_0 @ (u1_struct_0 @ X25))
% 6.13/6.33          | ~ (l1_struct_0 @ X25)
% 6.13/6.33          | ~ (v2_struct_0 @ X25))),
% 6.13/6.33      inference('cnf', [status(esa)], [fc1_struct_0])).
% 6.13/6.33  thf('56', plain,
% 6.13/6.33      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.13/6.33      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.13/6.33  thf(t17_xboole_1, axiom,
% 6.13/6.33    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 6.13/6.33  thf('57', plain,
% 6.13/6.33      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 6.13/6.33      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.13/6.33  thf(t3_xboole_1, axiom,
% 6.13/6.33    (![A:$i]:
% 6.13/6.33     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.13/6.33  thf('58', plain,
% 6.13/6.33      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 6.13/6.33      inference('cnf', [status(esa)], [t3_xboole_1])).
% 6.13/6.33  thf('59', plain,
% 6.13/6.33      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.13/6.33      inference('sup-', [status(thm)], ['57', '58'])).
% 6.13/6.33  thf('60', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i]:
% 6.13/6.33         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.13/6.33      inference('sup+', [status(thm)], ['56', '59'])).
% 6.13/6.33  thf('61', plain,
% 6.13/6.33      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.13/6.33      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.13/6.33  thf('62', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.13/6.33         (((X2) = (k3_xboole_0 @ X1 @ X0))
% 6.13/6.33          | ~ (v1_xboole_0 @ X1)
% 6.13/6.33          | ~ (v1_xboole_0 @ X2))),
% 6.13/6.33      inference('sup+', [status(thm)], ['60', '61'])).
% 6.13/6.33  thf('63', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.13/6.33         (~ (v2_struct_0 @ X0)
% 6.13/6.33          | ~ (l1_struct_0 @ X0)
% 6.13/6.33          | ~ (v1_xboole_0 @ X1)
% 6.13/6.33          | ((u1_struct_0 @ X0) = (k3_xboole_0 @ X1 @ X2)))),
% 6.13/6.33      inference('sup-', [status(thm)], ['55', '62'])).
% 6.13/6.33  thf('64', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i]:
% 6.13/6.33         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.13/6.33      inference('sup+', [status(thm)], ['56', '59'])).
% 6.13/6.33  thf('65', plain,
% 6.13/6.33      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.13/6.33      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.13/6.33  thf('66', plain,
% 6.13/6.33      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.13/6.33      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.13/6.33  thf(t4_subset_1, axiom,
% 6.13/6.33    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 6.13/6.33  thf('67', plain,
% 6.13/6.33      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 6.13/6.33      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.13/6.33  thf(d6_tex_2, axiom,
% 6.13/6.33    (![A:$i]:
% 6.13/6.33     ( ( l1_pre_topc @ A ) =>
% 6.13/6.33       ( ![B:$i]:
% 6.13/6.33         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.13/6.33           ( ( v2_tex_2 @ B @ A ) <=>
% 6.13/6.33             ( ![C:$i]:
% 6.13/6.33               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.13/6.33                 ( ~( ( r1_tarski @ C @ B ) & 
% 6.13/6.33                      ( ![D:$i]:
% 6.13/6.33                        ( ( m1_subset_1 @
% 6.13/6.33                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.13/6.33                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 6.13/6.33                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 6.13/6.33                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.13/6.33  thf('68', plain,
% 6.13/6.33      (![X35 : $i, X36 : $i]:
% 6.13/6.33         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 6.13/6.33          | (r1_tarski @ (sk_C @ X35 @ X36) @ X35)
% 6.13/6.33          | (v2_tex_2 @ X35 @ X36)
% 6.13/6.33          | ~ (l1_pre_topc @ X36))),
% 6.13/6.33      inference('cnf', [status(esa)], [d6_tex_2])).
% 6.13/6.33  thf('69', plain,
% 6.13/6.33      (![X0 : $i]:
% 6.13/6.33         (~ (l1_pre_topc @ X0)
% 6.13/6.33          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 6.13/6.33          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 6.13/6.33      inference('sup-', [status(thm)], ['67', '68'])).
% 6.13/6.33  thf('70', plain,
% 6.13/6.33      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 6.13/6.33      inference('cnf', [status(esa)], [t3_xboole_1])).
% 6.13/6.33  thf('71', plain,
% 6.13/6.33      (![X0 : $i]:
% 6.13/6.33         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 6.13/6.33          | ~ (l1_pre_topc @ X0)
% 6.13/6.33          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 6.13/6.33      inference('sup-', [status(thm)], ['69', '70'])).
% 6.13/6.33  thf('72', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i]:
% 6.13/6.33         ((v2_tex_2 @ X0 @ X1)
% 6.13/6.33          | ~ (v1_xboole_0 @ X0)
% 6.13/6.33          | ((sk_C @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 6.13/6.33          | ~ (l1_pre_topc @ X1))),
% 6.13/6.33      inference('sup+', [status(thm)], ['66', '71'])).
% 6.13/6.33  thf('73', plain,
% 6.13/6.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf(dt_k3_subset_1, axiom,
% 6.13/6.33    (![A:$i,B:$i]:
% 6.13/6.33     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.13/6.33       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.13/6.33  thf('74', plain,
% 6.13/6.33      (![X9 : $i, X10 : $i]:
% 6.13/6.33         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 6.13/6.33          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 6.13/6.33      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 6.13/6.33  thf('75', plain,
% 6.13/6.33      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 6.13/6.33        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.13/6.33      inference('sup-', [status(thm)], ['73', '74'])).
% 6.13/6.33  thf('76', plain,
% 6.13/6.33      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 6.13/6.33      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.13/6.33  thf('77', plain,
% 6.13/6.33      (![X35 : $i, X36 : $i, X38 : $i]:
% 6.13/6.33         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 6.13/6.33          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 6.13/6.33          | ~ (v4_pre_topc @ X38 @ X36)
% 6.13/6.33          | ((k9_subset_1 @ (u1_struct_0 @ X36) @ X35 @ X38)
% 6.13/6.33              != (sk_C @ X35 @ X36))
% 6.13/6.33          | (v2_tex_2 @ X35 @ X36)
% 6.13/6.33          | ~ (l1_pre_topc @ X36))),
% 6.13/6.33      inference('cnf', [status(esa)], [d6_tex_2])).
% 6.13/6.33  thf('78', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i]:
% 6.13/6.33         (~ (l1_pre_topc @ X0)
% 6.13/6.33          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 6.13/6.33          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 6.13/6.33              != (sk_C @ k1_xboole_0 @ X0))
% 6.13/6.33          | ~ (v4_pre_topc @ X1 @ X0)
% 6.13/6.33          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 6.13/6.33      inference('sup-', [status(thm)], ['76', '77'])).
% 6.13/6.33  thf('79', plain,
% 6.13/6.33      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 6.13/6.33      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.13/6.33  thf(commutativity_k9_subset_1, axiom,
% 6.13/6.33    (![A:$i,B:$i,C:$i]:
% 6.13/6.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.13/6.33       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 6.13/6.33  thf('80', plain,
% 6.13/6.33      (![X6 : $i, X7 : $i, X8 : $i]:
% 6.13/6.33         (((k9_subset_1 @ X6 @ X8 @ X7) = (k9_subset_1 @ X6 @ X7 @ X8))
% 6.13/6.33          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 6.13/6.33      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 6.13/6.33  thf('81', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i]:
% 6.13/6.33         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 6.13/6.33           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 6.13/6.33      inference('sup-', [status(thm)], ['79', '80'])).
% 6.13/6.33  thf('82', plain,
% 6.13/6.33      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 6.13/6.33      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.13/6.33  thf(redefinition_k9_subset_1, axiom,
% 6.13/6.33    (![A:$i,B:$i,C:$i]:
% 6.13/6.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.13/6.33       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 6.13/6.33  thf('83', plain,
% 6.13/6.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.13/6.33         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 6.13/6.33          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 6.13/6.33      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 6.13/6.33  thf('84', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i]:
% 6.13/6.33         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 6.13/6.33           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 6.13/6.33      inference('sup-', [status(thm)], ['82', '83'])).
% 6.13/6.33  thf(commutativity_k2_tarski, axiom,
% 6.13/6.33    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 6.13/6.33  thf('85', plain,
% 6.13/6.33      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 6.13/6.33      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 6.13/6.33  thf(t12_setfam_1, axiom,
% 6.13/6.33    (![A:$i,B:$i]:
% 6.13/6.33     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 6.13/6.33  thf('86', plain,
% 6.13/6.33      (![X15 : $i, X16 : $i]:
% 6.13/6.33         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 6.13/6.33      inference('cnf', [status(esa)], [t12_setfam_1])).
% 6.13/6.33  thf('87', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i]:
% 6.13/6.33         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 6.13/6.33      inference('sup+', [status(thm)], ['85', '86'])).
% 6.13/6.33  thf('88', plain,
% 6.13/6.33      (![X15 : $i, X16 : $i]:
% 6.13/6.33         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 6.13/6.33      inference('cnf', [status(esa)], [t12_setfam_1])).
% 6.13/6.33  thf('89', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.13/6.33      inference('sup+', [status(thm)], ['87', '88'])).
% 6.13/6.33  thf('90', plain,
% 6.13/6.33      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 6.13/6.33      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.13/6.33  thf('91', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 6.13/6.33      inference('sup+', [status(thm)], ['89', '90'])).
% 6.13/6.33  thf('92', plain,
% 6.13/6.33      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 6.13/6.33      inference('cnf', [status(esa)], [t3_xboole_1])).
% 6.13/6.33  thf('93', plain,
% 6.13/6.33      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 6.13/6.33      inference('sup-', [status(thm)], ['91', '92'])).
% 6.13/6.33  thf('94', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i]:
% 6.13/6.33         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.13/6.33      inference('demod', [status(thm)], ['84', '93'])).
% 6.13/6.33  thf('95', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i]:
% 6.13/6.33         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 6.13/6.33      inference('demod', [status(thm)], ['81', '94'])).
% 6.13/6.33  thf('96', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i]:
% 6.13/6.33         (~ (l1_pre_topc @ X0)
% 6.13/6.33          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 6.13/6.33          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 6.13/6.33          | ~ (v4_pre_topc @ X1 @ X0)
% 6.13/6.33          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 6.13/6.33      inference('demod', [status(thm)], ['78', '95'])).
% 6.13/6.33  thf('97', plain,
% 6.13/6.33      ((~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 6.13/6.33        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A))
% 6.13/6.33        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 6.13/6.33        | ~ (l1_pre_topc @ sk_A))),
% 6.13/6.33      inference('sup-', [status(thm)], ['75', '96'])).
% 6.13/6.33  thf('98', plain,
% 6.13/6.33      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 6.13/6.33        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.13/6.33      inference('sup-', [status(thm)], ['73', '74'])).
% 6.13/6.33  thf(t29_tops_1, axiom,
% 6.13/6.33    (![A:$i]:
% 6.13/6.33     ( ( l1_pre_topc @ A ) =>
% 6.13/6.33       ( ![B:$i]:
% 6.13/6.33         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.13/6.33           ( ( v4_pre_topc @ B @ A ) <=>
% 6.13/6.33             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 6.13/6.33  thf('99', plain,
% 6.13/6.33      (![X28 : $i, X29 : $i]:
% 6.13/6.33         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 6.13/6.33          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 6.13/6.33          | (v4_pre_topc @ X28 @ X29)
% 6.13/6.33          | ~ (l1_pre_topc @ X29))),
% 6.13/6.33      inference('cnf', [status(esa)], [t29_tops_1])).
% 6.13/6.33  thf('100', plain,
% 6.13/6.33      ((~ (l1_pre_topc @ sk_A)
% 6.13/6.33        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 6.13/6.33        | ~ (v3_pre_topc @ 
% 6.13/6.33             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.13/6.33              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 6.13/6.33             sk_A))),
% 6.13/6.33      inference('sup-', [status(thm)], ['98', '99'])).
% 6.13/6.33  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('102', plain,
% 6.13/6.33      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 6.13/6.33        | ~ (v3_pre_topc @ 
% 6.13/6.33             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.13/6.33              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 6.13/6.33             sk_A))),
% 6.13/6.33      inference('demod', [status(thm)], ['100', '101'])).
% 6.13/6.33  thf('103', plain,
% 6.13/6.33      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 6.13/6.33        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.13/6.33      inference('sup-', [status(thm)], ['73', '74'])).
% 6.13/6.33  thf('104', plain,
% 6.13/6.33      (![X9 : $i, X10 : $i]:
% 6.13/6.33         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 6.13/6.33          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 6.13/6.33      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 6.13/6.33  thf('105', plain,
% 6.13/6.33      ((m1_subset_1 @ 
% 6.13/6.33        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.13/6.33         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 6.13/6.33        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.13/6.33      inference('sup-', [status(thm)], ['103', '104'])).
% 6.13/6.33  thf(t17_tdlat_3, axiom,
% 6.13/6.33    (![A:$i]:
% 6.13/6.33     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.13/6.33       ( ( v1_tdlat_3 @ A ) <=>
% 6.13/6.33         ( ![B:$i]:
% 6.13/6.33           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.13/6.33             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 6.13/6.33  thf('106', plain,
% 6.13/6.33      (![X39 : $i, X40 : $i]:
% 6.13/6.33         (~ (v1_tdlat_3 @ X39)
% 6.13/6.33          | (v3_pre_topc @ X40 @ X39)
% 6.13/6.33          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 6.13/6.33          | ~ (l1_pre_topc @ X39)
% 6.13/6.33          | ~ (v2_pre_topc @ X39))),
% 6.13/6.33      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 6.13/6.33  thf('107', plain,
% 6.13/6.33      ((~ (v2_pre_topc @ sk_A)
% 6.13/6.33        | ~ (l1_pre_topc @ sk_A)
% 6.13/6.33        | (v3_pre_topc @ 
% 6.13/6.33           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.13/6.33            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 6.13/6.33           sk_A)
% 6.13/6.33        | ~ (v1_tdlat_3 @ sk_A))),
% 6.13/6.33      inference('sup-', [status(thm)], ['105', '106'])).
% 6.13/6.33  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('110', plain, ((v1_tdlat_3 @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('111', plain,
% 6.13/6.33      ((v3_pre_topc @ 
% 6.13/6.33        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.13/6.33         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 6.13/6.33        sk_A)),
% 6.13/6.33      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 6.13/6.33  thf('112', plain,
% 6.13/6.33      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 6.13/6.33      inference('demod', [status(thm)], ['102', '111'])).
% 6.13/6.33  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('114', plain,
% 6.13/6.33      ((((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A))
% 6.13/6.33        | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 6.13/6.33      inference('demod', [status(thm)], ['97', '112', '113'])).
% 6.13/6.33  thf('115', plain,
% 6.13/6.33      (![X0 : $i]:
% 6.13/6.33         (((k1_xboole_0) != (k1_xboole_0))
% 6.13/6.33          | ~ (l1_pre_topc @ sk_A)
% 6.13/6.33          | ~ (v1_xboole_0 @ X0)
% 6.13/6.33          | (v2_tex_2 @ X0 @ sk_A)
% 6.13/6.33          | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 6.13/6.33      inference('sup-', [status(thm)], ['72', '114'])).
% 6.13/6.33  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('117', plain,
% 6.13/6.33      (![X0 : $i]:
% 6.13/6.33         (((k1_xboole_0) != (k1_xboole_0))
% 6.13/6.33          | ~ (v1_xboole_0 @ X0)
% 6.13/6.33          | (v2_tex_2 @ X0 @ sk_A)
% 6.13/6.33          | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 6.13/6.33      inference('demod', [status(thm)], ['115', '116'])).
% 6.13/6.33  thf('118', plain,
% 6.13/6.33      (![X0 : $i]:
% 6.13/6.33         ((v2_tex_2 @ k1_xboole_0 @ sk_A)
% 6.13/6.33          | (v2_tex_2 @ X0 @ sk_A)
% 6.13/6.33          | ~ (v1_xboole_0 @ X0))),
% 6.13/6.33      inference('simplify', [status(thm)], ['117'])).
% 6.13/6.33  thf('119', plain,
% 6.13/6.33      ((~ (v1_xboole_0 @ k1_xboole_0) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 6.13/6.33      inference('eq_fact', [status(thm)], ['118'])).
% 6.13/6.33  thf('120', plain,
% 6.13/6.33      (![X0 : $i]:
% 6.13/6.33         (~ (v1_xboole_0 @ X0)
% 6.13/6.33          | ~ (v1_xboole_0 @ X0)
% 6.13/6.33          | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 6.13/6.33      inference('sup-', [status(thm)], ['65', '119'])).
% 6.13/6.33  thf('121', plain,
% 6.13/6.33      (![X0 : $i]: ((v2_tex_2 @ k1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 6.13/6.33      inference('simplify', [status(thm)], ['120'])).
% 6.13/6.33  thf('122', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.13/6.33         ((v2_tex_2 @ (k3_xboole_0 @ X1 @ X0) @ sk_A)
% 6.13/6.33          | ~ (v1_xboole_0 @ X1)
% 6.13/6.33          | ~ (v1_xboole_0 @ X2))),
% 6.13/6.33      inference('sup+', [status(thm)], ['64', '121'])).
% 6.13/6.33  thf('123', plain,
% 6.13/6.33      (![X0 : $i, X1 : $i]:
% 6.13/6.33         ((v2_tex_2 @ (k3_xboole_0 @ X1 @ X0) @ sk_A) | ~ (v1_xboole_0 @ X1))),
% 6.13/6.33      inference('condensation', [status(thm)], ['122'])).
% 6.13/6.33  thf('124', plain,
% 6.13/6.33      (![X0 : $i, X2 : $i]:
% 6.13/6.33         ((v2_tex_2 @ (u1_struct_0 @ X0) @ sk_A)
% 6.13/6.33          | ~ (v1_xboole_0 @ X2)
% 6.13/6.33          | ~ (l1_struct_0 @ X0)
% 6.13/6.33          | ~ (v2_struct_0 @ X0)
% 6.13/6.33          | ~ (v1_xboole_0 @ X2))),
% 6.13/6.33      inference('sup+', [status(thm)], ['63', '123'])).
% 6.13/6.33  thf('125', plain,
% 6.13/6.33      (![X0 : $i, X2 : $i]:
% 6.13/6.33         (~ (v2_struct_0 @ X0)
% 6.13/6.33          | ~ (l1_struct_0 @ X0)
% 6.13/6.33          | ~ (v1_xboole_0 @ X2)
% 6.13/6.33          | (v2_tex_2 @ (u1_struct_0 @ X0) @ sk_A))),
% 6.13/6.33      inference('simplify', [status(thm)], ['124'])).
% 6.13/6.33  thf('126', plain,
% 6.13/6.33      (![X0 : $i]:
% 6.13/6.33         ((v2_tex_2 @ sk_B_1 @ sk_A)
% 6.13/6.33          | ~ (v1_xboole_0 @ X0)
% 6.13/6.33          | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))
% 6.13/6.33          | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 6.13/6.33      inference('sup+', [status(thm)], ['54', '125'])).
% 6.13/6.33  thf('127', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))),
% 6.13/6.33      inference('sup-', [status(thm)], ['15', '16'])).
% 6.13/6.33  thf('128', plain,
% 6.13/6.33      (![X0 : $i]:
% 6.13/6.33         ((v2_tex_2 @ sk_B_1 @ sk_A)
% 6.13/6.33          | ~ (v1_xboole_0 @ X0)
% 6.13/6.33          | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 6.13/6.33      inference('demod', [status(thm)], ['126', '127'])).
% 6.13/6.33  thf('129', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 6.13/6.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.33  thf('130', plain,
% 6.13/6.33      (![X0 : $i]:
% 6.13/6.33         (~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))
% 6.13/6.33          | ~ (v1_xboole_0 @ X0))),
% 6.13/6.33      inference('clc', [status(thm)], ['128', '129'])).
% 6.13/6.33  thf('131', plain, ((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))),
% 6.13/6.33      inference('clc', [status(thm)], ['40', '41'])).
% 6.13/6.33  thf('132', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 6.13/6.33      inference('demod', [status(thm)], ['130', '131'])).
% 6.13/6.33  thf('133', plain, ($false), inference('sup-', [status(thm)], ['53', '132'])).
% 6.13/6.33  
% 6.13/6.33  % SZS output end Refutation
% 6.13/6.33  
% 6.13/6.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
