%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SqG0D5C24T

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:05 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 122 expanded)
%              Number of leaves         :   32 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  567 ( 954 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

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
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['1','4'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
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

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( m1_subset_1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X22 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
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

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_tex_2 @ X19 @ X20 )
      | ~ ( v2_tex_2 @ X21 @ X20 )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( X19 = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['5','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('40',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('44',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('47',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SqG0D5C24T
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 230 iterations in 0.175s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.41/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.62  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.41/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(t46_tex_2, conjecture,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( ( v1_xboole_0 @ B ) & 
% 0.41/0.62             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.62           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i]:
% 0.41/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.62            ( l1_pre_topc @ A ) ) =>
% 0.41/0.62          ( ![B:$i]:
% 0.41/0.62            ( ( ( v1_xboole_0 @ B ) & 
% 0.41/0.62                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.62              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.41/0.62  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('1', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('2', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(l13_xboole_0, axiom,
% 0.41/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.41/0.62  thf('4', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.62  thf('5', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['1', '4'])).
% 0.41/0.62  thf(d1_xboole_0, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.62  thf(d2_subset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( v1_xboole_0 @ A ) =>
% 0.41/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.41/0.62       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (![X6 : $i, X7 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X6 @ X7)
% 0.41/0.62          | (m1_subset_1 @ X6 @ X7)
% 0.41/0.62          | (v1_xboole_0 @ X7))),
% 0.41/0.62      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.41/0.62      inference('clc', [status(thm)], ['7', '8'])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['6', '9'])).
% 0.41/0.62  thf(redefinition_k6_domain_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.41/0.62       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (![X17 : $i, X18 : $i]:
% 0.41/0.62         ((v1_xboole_0 @ X17)
% 0.41/0.62          | ~ (m1_subset_1 @ X18 @ X17)
% 0.41/0.62          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v1_xboole_0 @ X0)
% 0.41/0.62          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.41/0.62          | (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.41/0.62          | (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['12'])).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['6', '9'])).
% 0.41/0.62  thf(t36_tex_2, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.62           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (![X22 : $i, X23 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.41/0.62          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X22) @ X23)
% 0.41/0.62          | ~ (l1_pre_topc @ X23)
% 0.41/0.62          | ~ (v2_pre_topc @ X23)
% 0.41/0.62          | (v2_struct_0 @ X23))),
% 0.41/0.62      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.41/0.62          | (v2_struct_0 @ X0)
% 0.41/0.62          | ~ (v2_pre_topc @ X0)
% 0.41/0.62          | ~ (l1_pre_topc @ X0)
% 0.41/0.62          | (v2_tex_2 @ 
% 0.41/0.62             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.41/0.62             X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.41/0.62          | ~ (l1_pre_topc @ X0)
% 0.41/0.62          | ~ (v2_pre_topc @ X0)
% 0.41/0.62          | (v2_struct_0 @ X0)
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['13', '16'])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v2_struct_0 @ X0)
% 0.41/0.62          | ~ (v2_pre_topc @ X0)
% 0.41/0.62          | ~ (l1_pre_topc @ X0)
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.41/0.62          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['17'])).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.41/0.62          | (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['12'])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['6', '9'])).
% 0.41/0.62  thf(dt_k6_domain_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.41/0.62       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i]:
% 0.41/0.62         ((v1_xboole_0 @ X15)
% 0.41/0.62          | ~ (m1_subset_1 @ X16 @ X15)
% 0.41/0.62          | (m1_subset_1 @ (k6_domain_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15)))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v1_xboole_0 @ X0)
% 0.41/0.62          | (m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ 
% 0.41/0.62             (k1_zfmisc_1 @ X0))
% 0.41/0.62          | (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.41/0.62          | (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['22'])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.41/0.62          | (v1_xboole_0 @ X0)
% 0.41/0.62          | (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['19', '23'])).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v1_xboole_0 @ X0)
% 0.41/0.62          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.41/0.62  thf(t4_subset_1, axiom,
% 0.41/0.62    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.41/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.62  thf(d7_tex_2, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( l1_pre_topc @ A ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.62           ( ( v3_tex_2 @ B @ A ) <=>
% 0.41/0.62             ( ( v2_tex_2 @ B @ A ) & 
% 0.41/0.62               ( ![C:$i]:
% 0.41/0.62                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.62                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.41/0.62                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.62  thf('27', plain,
% 0.41/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.41/0.62          | ~ (v3_tex_2 @ X19 @ X20)
% 0.41/0.62          | ~ (v2_tex_2 @ X21 @ X20)
% 0.41/0.62          | ~ (r1_tarski @ X19 @ X21)
% 0.41/0.62          | ((X19) = (X21))
% 0.41/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.41/0.62          | ~ (l1_pre_topc @ X20))),
% 0.41/0.62      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.41/0.62  thf('28', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (l1_pre_topc @ X0)
% 0.41/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.62          | ((k1_xboole_0) = (X1))
% 0.41/0.62          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.41/0.62          | ~ (v2_tex_2 @ X1 @ X0)
% 0.41/0.62          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.62  thf('29', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.41/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (l1_pre_topc @ X0)
% 0.41/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.62          | ((k1_xboole_0) = (X1))
% 0.41/0.62          | ~ (v2_tex_2 @ X1 @ X0)
% 0.41/0.62          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.41/0.62          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.41/0.62          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.41/0.62          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.41/0.62          | ~ (l1_pre_topc @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['25', '30'])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.41/0.62          | ~ (l1_pre_topc @ X0)
% 0.41/0.62          | ~ (v2_pre_topc @ X0)
% 0.41/0.62          | (v2_struct_0 @ X0)
% 0.41/0.62          | ~ (l1_pre_topc @ X0)
% 0.41/0.62          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.41/0.62          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['18', '31'])).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.41/0.62          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.41/0.62          | (v2_struct_0 @ X0)
% 0.41/0.62          | ~ (v2_pre_topc @ X0)
% 0.41/0.62          | ~ (l1_pre_topc @ X0)
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['32'])).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ sk_A)))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['5', '33'])).
% 0.41/0.62  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('37', plain,
% 0.41/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ sk_A)))))),
% 0.41/0.62      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.41/0.62  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      ((((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ sk_A))))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('clc', [status(thm)], ['37', '38'])).
% 0.41/0.62  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.41/0.62  thf('40', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.41/0.62  thf('41', plain,
% 0.41/0.62      ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.41/0.62  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.62  thf('43', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['41', '42'])).
% 0.41/0.62  thf(fc2_struct_0, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.62       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.62  thf('44', plain,
% 0.41/0.62      (![X14 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.41/0.62          | ~ (l1_struct_0 @ X14)
% 0.41/0.62          | (v2_struct_0 @ X14))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.41/0.62  thf('45', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.41/0.62  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(dt_l1_pre_topc, axiom,
% 0.41/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.62  thf('47', plain,
% 0.41/0.62      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.62  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.62  thf('49', plain, ((v2_struct_0 @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['45', '48'])).
% 0.41/0.62  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.48/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
