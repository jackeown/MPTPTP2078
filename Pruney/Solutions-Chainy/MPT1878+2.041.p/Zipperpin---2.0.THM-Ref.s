%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BWtqaSjkkn

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:08 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 104 expanded)
%              Number of leaves         :   33 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  473 ( 752 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
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
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
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

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_tex_2 @ X18 @ X19 )
      | ~ ( v2_tex_2 @ X20 @ X19 )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( X18 = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','31'])).

thf('33',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('41',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('44',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BWtqaSjkkn
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:48:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 1.02/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.02/1.21  % Solved by: fo/fo7.sh
% 1.02/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.21  % done 685 iterations in 0.746s
% 1.02/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.02/1.21  % SZS output start Refutation
% 1.02/1.21  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.02/1.21  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.02/1.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.02/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.02/1.21  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.02/1.21  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 1.02/1.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.02/1.21  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.02/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.02/1.21  thf(sk_B_type, type, sk_B: $i > $i).
% 1.02/1.21  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.02/1.21  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.02/1.21  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.02/1.21  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.02/1.21  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.02/1.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.02/1.21  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.02/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.02/1.21  thf(t46_tex_2, conjecture,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( ( v1_xboole_0 @ B ) & 
% 1.02/1.21             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.02/1.21           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 1.02/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.21    (~( ![A:$i]:
% 1.02/1.21        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.02/1.21            ( l1_pre_topc @ A ) ) =>
% 1.02/1.21          ( ![B:$i]:
% 1.02/1.21            ( ( ( v1_xboole_0 @ B ) & 
% 1.02/1.21                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.02/1.21              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 1.02/1.21    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 1.02/1.21  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(l13_xboole_0, axiom,
% 1.02/1.21    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.02/1.21  thf('1', plain,
% 1.02/1.21      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.02/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.02/1.21  thf('2', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('3', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('4', plain,
% 1.02/1.21      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.02/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.02/1.21  thf('5', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['3', '4'])).
% 1.02/1.21  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.02/1.21      inference('demod', [status(thm)], ['2', '5'])).
% 1.02/1.21  thf('7', plain,
% 1.02/1.21      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 1.02/1.21      inference('sup+', [status(thm)], ['1', '6'])).
% 1.02/1.21  thf(existence_m1_subset_1, axiom,
% 1.02/1.21    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 1.02/1.21  thf('8', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 1.02/1.21      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 1.02/1.21  thf(redefinition_k6_domain_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.02/1.21       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.02/1.21  thf('9', plain,
% 1.02/1.21      (![X16 : $i, X17 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ X16)
% 1.02/1.21          | ~ (m1_subset_1 @ X17 @ X16)
% 1.02/1.21          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 1.02/1.21      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.02/1.21  thf('10', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.02/1.21          | (v1_xboole_0 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['8', '9'])).
% 1.02/1.21  thf('11', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 1.02/1.21      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 1.02/1.21  thf(t36_tex_2, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.02/1.21           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 1.02/1.21  thf('12', plain,
% 1.02/1.21      (![X21 : $i, X22 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 1.02/1.21          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X22) @ X21) @ X22)
% 1.02/1.21          | ~ (l1_pre_topc @ X22)
% 1.02/1.21          | ~ (v2_pre_topc @ X22)
% 1.02/1.21          | (v2_struct_0 @ X22))),
% 1.02/1.21      inference('cnf', [status(esa)], [t36_tex_2])).
% 1.02/1.21  thf('13', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v2_struct_0 @ X0)
% 1.02/1.21          | ~ (v2_pre_topc @ X0)
% 1.02/1.21          | ~ (l1_pre_topc @ X0)
% 1.02/1.21          | (v2_tex_2 @ 
% 1.02/1.21             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 1.02/1.21             X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['11', '12'])).
% 1.02/1.21  thf('14', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.02/1.21          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.02/1.21          | ~ (l1_pre_topc @ X0)
% 1.02/1.21          | ~ (v2_pre_topc @ X0)
% 1.02/1.21          | (v2_struct_0 @ X0))),
% 1.02/1.21      inference('sup+', [status(thm)], ['10', '13'])).
% 1.02/1.21  thf('15', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 1.02/1.21      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 1.02/1.21  thf(t2_subset, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( m1_subset_1 @ A @ B ) =>
% 1.02/1.21       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.02/1.21  thf('16', plain,
% 1.02/1.21      (![X9 : $i, X10 : $i]:
% 1.02/1.21         ((r2_hidden @ X9 @ X10)
% 1.02/1.21          | (v1_xboole_0 @ X10)
% 1.02/1.21          | ~ (m1_subset_1 @ X9 @ X10))),
% 1.02/1.21      inference('cnf', [status(esa)], [t2_subset])).
% 1.02/1.21  thf('17', plain,
% 1.02/1.21      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['15', '16'])).
% 1.02/1.21  thf(t63_subset_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( r2_hidden @ A @ B ) =>
% 1.02/1.21       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.02/1.21  thf('18', plain,
% 1.02/1.21      (![X7 : $i, X8 : $i]:
% 1.02/1.21         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 1.02/1.21          | ~ (r2_hidden @ X7 @ X8))),
% 1.02/1.21      inference('cnf', [status(esa)], [t63_subset_1])).
% 1.02/1.21  thf('19', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ X0)
% 1.02/1.21          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['17', '18'])).
% 1.02/1.21  thf(t4_subset_1, axiom,
% 1.02/1.21    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.02/1.21  thf('20', plain,
% 1.02/1.21      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 1.02/1.21      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.02/1.21  thf(d7_tex_2, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( l1_pre_topc @ A ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21           ( ( v3_tex_2 @ B @ A ) <=>
% 1.02/1.21             ( ( v2_tex_2 @ B @ A ) & 
% 1.02/1.21               ( ![C:$i]:
% 1.02/1.21                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.02/1.21                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 1.02/1.21  thf('21', plain,
% 1.02/1.21      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.02/1.21          | ~ (v3_tex_2 @ X18 @ X19)
% 1.02/1.21          | ~ (v2_tex_2 @ X20 @ X19)
% 1.02/1.21          | ~ (r1_tarski @ X18 @ X20)
% 1.02/1.21          | ((X18) = (X20))
% 1.02/1.21          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.02/1.21          | ~ (l1_pre_topc @ X19))),
% 1.02/1.21      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.02/1.21  thf('22', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         (~ (l1_pre_topc @ X0)
% 1.02/1.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.02/1.21          | ((k1_xboole_0) = (X1))
% 1.02/1.21          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 1.02/1.21          | ~ (v2_tex_2 @ X1 @ X0)
% 1.02/1.21          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['20', '21'])).
% 1.02/1.21  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.02/1.21  thf('23', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 1.02/1.21      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.02/1.21  thf('24', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         (~ (l1_pre_topc @ X0)
% 1.02/1.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.02/1.21          | ((k1_xboole_0) = (X1))
% 1.02/1.21          | ~ (v2_tex_2 @ X1 @ X0)
% 1.02/1.21          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 1.02/1.21      inference('demod', [status(thm)], ['22', '23'])).
% 1.02/1.21  thf('25', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.02/1.21          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.02/1.21          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.02/1.21          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 1.02/1.21          | ~ (l1_pre_topc @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['19', '24'])).
% 1.02/1.21  thf(t1_boole, axiom,
% 1.02/1.21    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.02/1.21  thf('26', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 1.02/1.21      inference('cnf', [status(esa)], [t1_boole])).
% 1.02/1.21  thf(t49_zfmisc_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 1.02/1.21  thf('27', plain,
% 1.02/1.21      (![X3 : $i, X4 : $i]:
% 1.02/1.21         ((k2_xboole_0 @ (k1_tarski @ X3) @ X4) != (k1_xboole_0))),
% 1.02/1.21      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 1.02/1.21  thf('28', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['26', '27'])).
% 1.02/1.21  thf('29', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.02/1.21          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.02/1.21          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.02/1.21          | ~ (l1_pre_topc @ X0))),
% 1.02/1.21      inference('simplify_reflect-', [status(thm)], ['25', '28'])).
% 1.02/1.21  thf('30', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v2_struct_0 @ X0)
% 1.02/1.21          | ~ (v2_pre_topc @ X0)
% 1.02/1.21          | ~ (l1_pre_topc @ X0)
% 1.02/1.21          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.02/1.21          | ~ (l1_pre_topc @ X0)
% 1.02/1.21          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.02/1.21          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['14', '29'])).
% 1.02/1.21  thf('31', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.02/1.21          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.02/1.21          | ~ (l1_pre_topc @ X0)
% 1.02/1.21          | ~ (v2_pre_topc @ X0)
% 1.02/1.21          | (v2_struct_0 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['30'])).
% 1.02/1.21  thf('32', plain,
% 1.02/1.21      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.02/1.21        | (v2_struct_0 @ sk_A)
% 1.02/1.21        | ~ (v2_pre_topc @ sk_A)
% 1.02/1.21        | ~ (l1_pre_topc @ sk_A)
% 1.02/1.21        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['7', '31'])).
% 1.02/1.21  thf('33', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('34', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['3', '4'])).
% 1.02/1.21  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.02/1.21      inference('demod', [status(thm)], ['33', '34'])).
% 1.02/1.21  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('38', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('demod', [status(thm)], ['32', '35', '36', '37'])).
% 1.02/1.21  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('40', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.02/1.21      inference('clc', [status(thm)], ['38', '39'])).
% 1.02/1.21  thf(fc2_struct_0, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.02/1.21       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.02/1.21  thf('41', plain,
% 1.02/1.21      (![X15 : $i]:
% 1.02/1.21         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 1.02/1.21          | ~ (l1_struct_0 @ X15)
% 1.02/1.21          | (v2_struct_0 @ X15))),
% 1.02/1.21      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.02/1.21  thf('42', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 1.02/1.21      inference('sup-', [status(thm)], ['40', '41'])).
% 1.02/1.21  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(dt_l1_pre_topc, axiom,
% 1.02/1.21    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.02/1.21  thf('44', plain,
% 1.02/1.21      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.02/1.21  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 1.02/1.21      inference('sup-', [status(thm)], ['43', '44'])).
% 1.02/1.21  thf('46', plain, ((v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('demod', [status(thm)], ['42', '45'])).
% 1.02/1.21  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 1.02/1.21  
% 1.02/1.21  % SZS output end Refutation
% 1.02/1.21  
% 1.02/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
