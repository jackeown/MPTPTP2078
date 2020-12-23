%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DWCKizbhPw

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 112 expanded)
%              Number of leaves         :   32 (  47 expanded)
%              Depth                    :   17
%              Number of atoms          :  535 ( 906 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t46_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( v3_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['1','4'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('14',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_tex_2 @ X17 @ X18 )
      | ~ ( v2_tex_2 @ X19 @ X18 )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( X17 = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['34','35'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DWCKizbhPw
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:09:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 99 iterations in 0.059s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.52  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.22/0.52  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(t46_tex_2, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( v1_xboole_0 @ B ) & 
% 0.22/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.52           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.52            ( l1_pre_topc @ A ) ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( ( v1_xboole_0 @ B ) & 
% 0.22/0.52                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.52              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.22/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('2', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(l13_xboole_0, axiom,
% 0.22/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.52  thf('4', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('5', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['1', '4'])).
% 0.22/0.52  thf(existence_m1_subset_1, axiom,
% 0.22/0.52    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.22/0.52  thf('6', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.22/0.52      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.22/0.52  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.52       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ X15)
% 0.22/0.52          | ~ (m1_subset_1 @ X16 @ X15)
% 0.22/0.52          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.22/0.52          | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('9', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.22/0.52      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.22/0.52  thf(t36_tex_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.22/0.52          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.22/0.52          | ~ (l1_pre_topc @ X21)
% 0.22/0.52          | ~ (v2_pre_topc @ X21)
% 0.22/0.52          | (v2_struct_0 @ X21))),
% 0.22/0.52      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v2_tex_2 @ 
% 0.22/0.52             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.22/0.52             X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.22/0.52          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['8', '11'])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.22/0.52          | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('14', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.22/0.52      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.22/0.52  thf(dt_k6_domain_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.52       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ X13)
% 0.22/0.52          | ~ (m1_subset_1 @ X14 @ X13)
% 0.22/0.52          | (m1_subset_1 @ (k6_domain_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.22/0.52          | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.22/0.52          | (v1_xboole_0 @ X0)
% 0.22/0.52          | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['13', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ X0)
% 0.22/0.52          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.52  thf(t4_subset_1, axiom,
% 0.22/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.52  thf(d7_tex_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.52             ( ( v2_tex_2 @ B @ A ) & 
% 0.22/0.52               ( ![C:$i]:
% 0.22/0.52                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.52                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.52          | ~ (v3_tex_2 @ X17 @ X18)
% 0.22/0.52          | ~ (v2_tex_2 @ X19 @ X18)
% 0.22/0.52          | ~ (r1_tarski @ X17 @ X19)
% 0.22/0.52          | ((X17) = (X19))
% 0.22/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.52          | ~ (l1_pre_topc @ X18))),
% 0.22/0.52      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.52          | ((k1_xboole_0) = (X1))
% 0.22/0.52          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.22/0.52          | ~ (v2_tex_2 @ X1 @ X0)
% 0.22/0.52          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.52  thf('22', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.52          | ((k1_xboole_0) = (X1))
% 0.22/0.52          | ~ (v2_tex_2 @ X1 @ X0)
% 0.22/0.52          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.52          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.22/0.52          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.22/0.52          | ~ (l1_pre_topc @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '23'])).
% 0.22/0.52  thf(t1_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.52  thf('25', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.52  thf(t49_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ (k1_tarski @ X3) @ X4) != (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.22/0.52  thf('27', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.52          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['24', '27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.52          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '28'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.52          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '30'])).
% 0.22/0.52  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.22/0.52  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('36', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf(rc7_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ?[B:$i]:
% 0.22/0.52         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.52           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X12 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (sk_B_1 @ X12) @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.52          | ~ (l1_pre_topc @ X12)
% 0.22/0.52          | ~ (v2_pre_topc @ X12)
% 0.22/0.52          | (v2_struct_0 @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.22/0.52  thf(cc1_subset_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_xboole_0 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.22/0.52          | (v1_xboole_0 @ X7)
% 0.22/0.52          | ~ (v1_xboole_0 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.22/0.52          | (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.22/0.52  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('43', plain, (((v1_xboole_0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.22/0.52  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('45', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 0.22/0.52      inference('clc', [status(thm)], ['43', '44'])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (![X12 : $i]:
% 0.22/0.52         (~ (v1_xboole_0 @ (sk_B_1 @ X12))
% 0.22/0.52          | ~ (l1_pre_topc @ X12)
% 0.22/0.52          | ~ (v2_pre_topc @ X12)
% 0.22/0.52          | (v2_struct_0 @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.52  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('50', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.22/0.52  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.38/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
