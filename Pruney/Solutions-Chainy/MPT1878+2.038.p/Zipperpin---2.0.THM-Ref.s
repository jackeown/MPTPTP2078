%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QGIGjfa43n

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:08 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 115 expanded)
%              Number of leaves         :   35 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  526 ( 834 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X22 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('16',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
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

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_tex_2 @ X19 @ X20 )
      | ~ ( v2_tex_2 @ X21 @ X20 )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( X19 = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','36'])).

thf('38',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('49',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QGIGjfa43n
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.07/1.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.28  % Solved by: fo/fo7.sh
% 1.07/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.28  % done 1350 iterations in 0.840s
% 1.07/1.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.28  % SZS output start Refutation
% 1.07/1.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.28  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.07/1.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.07/1.28  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.07/1.28  thf(sk_B_type, type, sk_B: $i > $i).
% 1.07/1.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.07/1.28  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.07/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.28  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.07/1.28  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.07/1.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.28  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 1.07/1.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.28  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.07/1.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.28  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.07/1.28  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.07/1.28  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.07/1.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.07/1.28  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.07/1.28  thf(t46_tex_2, conjecture,
% 1.07/1.28    (![A:$i]:
% 1.07/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.28       ( ![B:$i]:
% 1.07/1.28         ( ( ( v1_xboole_0 @ B ) & 
% 1.07/1.28             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.07/1.28           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 1.07/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.28    (~( ![A:$i]:
% 1.07/1.28        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.07/1.28            ( l1_pre_topc @ A ) ) =>
% 1.07/1.28          ( ![B:$i]:
% 1.07/1.28            ( ( ( v1_xboole_0 @ B ) & 
% 1.07/1.28                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.07/1.28              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 1.07/1.28    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 1.07/1.28  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf(l13_xboole_0, axiom,
% 1.07/1.28    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.07/1.28  thf('1', plain,
% 1.07/1.28      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.28      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.07/1.28  thf('2', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('3', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('4', plain,
% 1.07/1.28      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.28      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.07/1.28  thf('5', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.07/1.28      inference('sup-', [status(thm)], ['3', '4'])).
% 1.07/1.28  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.07/1.28      inference('demod', [status(thm)], ['2', '5'])).
% 1.07/1.28  thf('7', plain,
% 1.07/1.28      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['1', '6'])).
% 1.07/1.28  thf(existence_m1_subset_1, axiom,
% 1.07/1.28    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 1.07/1.28  thf('8', plain, (![X8 : $i]: (m1_subset_1 @ (sk_B @ X8) @ X8)),
% 1.07/1.28      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 1.07/1.28  thf(redefinition_k6_domain_1, axiom,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.07/1.28       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.07/1.28  thf('9', plain,
% 1.07/1.28      (![X17 : $i, X18 : $i]:
% 1.07/1.28         ((v1_xboole_0 @ X17)
% 1.07/1.28          | ~ (m1_subset_1 @ X18 @ X17)
% 1.07/1.28          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 1.07/1.28      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.07/1.28  thf('10', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.07/1.28          | (v1_xboole_0 @ X0))),
% 1.07/1.28      inference('sup-', [status(thm)], ['8', '9'])).
% 1.07/1.28  thf('11', plain, (![X8 : $i]: (m1_subset_1 @ (sk_B @ X8) @ X8)),
% 1.07/1.28      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 1.07/1.28  thf(t36_tex_2, axiom,
% 1.07/1.28    (![A:$i]:
% 1.07/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.28       ( ![B:$i]:
% 1.07/1.28         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.07/1.28           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 1.07/1.28  thf('12', plain,
% 1.07/1.28      (![X22 : $i, X23 : $i]:
% 1.07/1.28         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 1.07/1.28          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X22) @ X23)
% 1.07/1.28          | ~ (l1_pre_topc @ X23)
% 1.07/1.28          | ~ (v2_pre_topc @ X23)
% 1.07/1.28          | (v2_struct_0 @ X23))),
% 1.07/1.28      inference('cnf', [status(esa)], [t36_tex_2])).
% 1.07/1.28  thf('13', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((v2_struct_0 @ X0)
% 1.07/1.28          | ~ (v2_pre_topc @ X0)
% 1.07/1.28          | ~ (l1_pre_topc @ X0)
% 1.07/1.28          | (v2_tex_2 @ 
% 1.07/1.28             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 1.07/1.28             X0))),
% 1.07/1.28      inference('sup-', [status(thm)], ['11', '12'])).
% 1.07/1.28  thf('14', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.07/1.28          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.07/1.28          | ~ (l1_pre_topc @ X0)
% 1.07/1.28          | ~ (v2_pre_topc @ X0)
% 1.07/1.28          | (v2_struct_0 @ X0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['10', '13'])).
% 1.07/1.28  thf('15', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.07/1.28          | (v1_xboole_0 @ X0))),
% 1.07/1.28      inference('sup-', [status(thm)], ['8', '9'])).
% 1.07/1.28  thf('16', plain, (![X8 : $i]: (m1_subset_1 @ (sk_B @ X8) @ X8)),
% 1.07/1.28      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 1.07/1.28  thf(dt_k6_domain_1, axiom,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.07/1.28       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.07/1.28  thf('17', plain,
% 1.07/1.28      (![X15 : $i, X16 : $i]:
% 1.07/1.28         ((v1_xboole_0 @ X15)
% 1.07/1.28          | ~ (m1_subset_1 @ X16 @ X15)
% 1.07/1.28          | (m1_subset_1 @ (k6_domain_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15)))),
% 1.07/1.28      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 1.07/1.28  thf('18', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 1.07/1.28          | (v1_xboole_0 @ X0))),
% 1.07/1.28      inference('sup-', [status(thm)], ['16', '17'])).
% 1.07/1.28  thf('19', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 1.07/1.28          | (v1_xboole_0 @ X0)
% 1.07/1.28          | (v1_xboole_0 @ X0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['15', '18'])).
% 1.07/1.28  thf('20', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((v1_xboole_0 @ X0)
% 1.07/1.28          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 1.07/1.28      inference('simplify', [status(thm)], ['19'])).
% 1.07/1.28  thf(t4_subset_1, axiom,
% 1.07/1.28    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.07/1.28  thf('21', plain,
% 1.07/1.28      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 1.07/1.28      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.07/1.28  thf(d7_tex_2, axiom,
% 1.07/1.28    (![A:$i]:
% 1.07/1.28     ( ( l1_pre_topc @ A ) =>
% 1.07/1.28       ( ![B:$i]:
% 1.07/1.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.28           ( ( v3_tex_2 @ B @ A ) <=>
% 1.07/1.28             ( ( v2_tex_2 @ B @ A ) & 
% 1.07/1.28               ( ![C:$i]:
% 1.07/1.28                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.28                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.07/1.28                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 1.07/1.28  thf('22', plain,
% 1.07/1.28      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.07/1.28         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.07/1.28          | ~ (v3_tex_2 @ X19 @ X20)
% 1.07/1.28          | ~ (v2_tex_2 @ X21 @ X20)
% 1.07/1.28          | ~ (r1_tarski @ X19 @ X21)
% 1.07/1.28          | ((X19) = (X21))
% 1.07/1.28          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.07/1.28          | ~ (l1_pre_topc @ X20))),
% 1.07/1.28      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.07/1.28  thf('23', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         (~ (l1_pre_topc @ X0)
% 1.07/1.28          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.07/1.28          | ((k1_xboole_0) = (X1))
% 1.07/1.28          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 1.07/1.28          | ~ (v2_tex_2 @ X1 @ X0)
% 1.07/1.28          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 1.07/1.28      inference('sup-', [status(thm)], ['21', '22'])).
% 1.07/1.28  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.07/1.28  thf('24', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 1.07/1.28      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.07/1.28  thf('25', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         (~ (l1_pre_topc @ X0)
% 1.07/1.28          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.07/1.28          | ((k1_xboole_0) = (X1))
% 1.07/1.28          | ~ (v2_tex_2 @ X1 @ X0)
% 1.07/1.28          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['23', '24'])).
% 1.07/1.28  thf('26', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.07/1.28          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.07/1.28          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.07/1.28          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 1.07/1.28          | ~ (l1_pre_topc @ X0))),
% 1.07/1.28      inference('sup-', [status(thm)], ['20', '25'])).
% 1.07/1.28  thf(t4_boole, axiom,
% 1.07/1.28    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.07/1.28  thf('27', plain,
% 1.07/1.28      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 1.07/1.28      inference('cnf', [status(esa)], [t4_boole])).
% 1.07/1.28  thf(t98_xboole_1, axiom,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.07/1.28  thf('28', plain,
% 1.07/1.28      (![X4 : $i, X5 : $i]:
% 1.07/1.28         ((k2_xboole_0 @ X4 @ X5)
% 1.07/1.28           = (k5_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4)))),
% 1.07/1.28      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.07/1.28  thf('29', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['27', '28'])).
% 1.07/1.28  thf(t5_boole, axiom,
% 1.07/1.28    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.07/1.28  thf('30', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 1.07/1.28      inference('cnf', [status(esa)], [t5_boole])).
% 1.07/1.28  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['29', '30'])).
% 1.07/1.28  thf(t49_zfmisc_1, axiom,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 1.07/1.28  thf('32', plain,
% 1.07/1.28      (![X6 : $i, X7 : $i]:
% 1.07/1.28         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 1.07/1.28      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 1.07/1.28  thf('33', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 1.07/1.28      inference('sup-', [status(thm)], ['31', '32'])).
% 1.07/1.28  thf('34', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.07/1.28          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.07/1.28          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.07/1.28          | ~ (l1_pre_topc @ X0))),
% 1.07/1.28      inference('simplify_reflect-', [status(thm)], ['26', '33'])).
% 1.07/1.28  thf('35', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((v2_struct_0 @ X0)
% 1.07/1.28          | ~ (v2_pre_topc @ X0)
% 1.07/1.28          | ~ (l1_pre_topc @ X0)
% 1.07/1.28          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.07/1.28          | ~ (l1_pre_topc @ X0)
% 1.07/1.28          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.07/1.28          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['14', '34'])).
% 1.07/1.28  thf('36', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.07/1.28          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.07/1.28          | ~ (l1_pre_topc @ X0)
% 1.07/1.28          | ~ (v2_pre_topc @ X0)
% 1.07/1.28          | (v2_struct_0 @ X0))),
% 1.07/1.28      inference('simplify', [status(thm)], ['35'])).
% 1.07/1.28  thf('37', plain,
% 1.07/1.28      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.07/1.28        | (v2_struct_0 @ sk_A)
% 1.07/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.07/1.28        | ~ (l1_pre_topc @ sk_A)
% 1.07/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['7', '36'])).
% 1.07/1.28  thf('38', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('39', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.07/1.28      inference('sup-', [status(thm)], ['3', '4'])).
% 1.07/1.28  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.28      inference('demod', [status(thm)], ['38', '39'])).
% 1.07/1.28  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('43', plain,
% 1.07/1.28      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.28      inference('demod', [status(thm)], ['37', '40', '41', '42'])).
% 1.07/1.28  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('45', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.07/1.28      inference('clc', [status(thm)], ['43', '44'])).
% 1.07/1.28  thf(fc2_struct_0, axiom,
% 1.07/1.28    (![A:$i]:
% 1.07/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.07/1.28       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.07/1.28  thf('46', plain,
% 1.07/1.28      (![X14 : $i]:
% 1.07/1.28         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 1.07/1.28          | ~ (l1_struct_0 @ X14)
% 1.07/1.28          | (v2_struct_0 @ X14))),
% 1.07/1.28      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.07/1.28  thf('47', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 1.07/1.28      inference('sup-', [status(thm)], ['45', '46'])).
% 1.07/1.28  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf(dt_l1_pre_topc, axiom,
% 1.07/1.28    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.07/1.28  thf('49', plain,
% 1.07/1.28      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 1.07/1.28      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.07/1.28  thf('50', plain, ((l1_struct_0 @ sk_A)),
% 1.07/1.28      inference('sup-', [status(thm)], ['48', '49'])).
% 1.07/1.28  thf('51', plain, ((v2_struct_0 @ sk_A)),
% 1.07/1.28      inference('demod', [status(thm)], ['47', '50'])).
% 1.07/1.28  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 1.07/1.28  
% 1.07/1.28  % SZS output end Refutation
% 1.07/1.28  
% 1.07/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
