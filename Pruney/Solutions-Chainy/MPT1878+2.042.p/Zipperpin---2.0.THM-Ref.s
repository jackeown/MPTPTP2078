%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0xQFN2Sysv

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:09 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 110 expanded)
%              Number of leaves         :   35 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  566 ( 844 expanded)
%              Number of equality atoms :   44 (  52 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ X24 ) @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('24',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
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

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_tex_2 @ X21 @ X22 )
      | ~ ( v2_tex_2 @ X23 @ X22 )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ( X21 = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','35'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['40','41'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('43',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('47',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['44','45','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0xQFN2Sysv
% 0.12/0.35  % Computer   : n006.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 14:26:23 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.68/1.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.68/1.91  % Solved by: fo/fo7.sh
% 1.68/1.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.68/1.91  % done 1186 iterations in 1.447s
% 1.68/1.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.68/1.91  % SZS output start Refutation
% 1.68/1.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.68/1.91  thf(sk_A_type, type, sk_A: $i).
% 1.68/1.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.68/1.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.68/1.91  thf(sk_B_type, type, sk_B: $i > $i).
% 1.68/1.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.68/1.91  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.68/1.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.68/1.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.68/1.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.68/1.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.68/1.91  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.68/1.91  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.68/1.91  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.68/1.91  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.68/1.91  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.68/1.91  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 1.68/1.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.68/1.91  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.68/1.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.68/1.91  thf(t46_tex_2, conjecture,
% 1.68/1.91    (![A:$i]:
% 1.68/1.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.68/1.91       ( ![B:$i]:
% 1.68/1.91         ( ( ( v1_xboole_0 @ B ) & 
% 1.68/1.91             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.68/1.91           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 1.68/1.91  thf(zf_stmt_0, negated_conjecture,
% 1.68/1.91    (~( ![A:$i]:
% 1.68/1.91        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.68/1.91            ( l1_pre_topc @ A ) ) =>
% 1.68/1.91          ( ![B:$i]:
% 1.68/1.91            ( ( ( v1_xboole_0 @ B ) & 
% 1.68/1.91                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.68/1.91              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 1.68/1.91    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 1.68/1.91  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.68/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.91  thf(l13_xboole_0, axiom,
% 1.68/1.91    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.68/1.91  thf('1', plain,
% 1.68/1.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.68/1.91      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.68/1.91  thf('2', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 1.68/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.91  thf('3', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.68/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.91  thf('4', plain,
% 1.68/1.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.68/1.91      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.68/1.91  thf('5', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.68/1.91      inference('sup-', [status(thm)], ['3', '4'])).
% 1.68/1.91  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.68/1.91      inference('demod', [status(thm)], ['2', '5'])).
% 1.68/1.91  thf('7', plain,
% 1.68/1.91      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 1.68/1.91      inference('sup+', [status(thm)], ['1', '6'])).
% 1.68/1.91  thf(t29_mcart_1, axiom,
% 1.68/1.91    (![A:$i]:
% 1.68/1.91     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.68/1.91          ( ![B:$i]:
% 1.68/1.91            ( ~( ( r2_hidden @ B @ A ) & 
% 1.68/1.91                 ( ![C:$i,D:$i,E:$i]:
% 1.68/1.91                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 1.68/1.91                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 1.68/1.91  thf('8', plain,
% 1.68/1.91      (![X13 : $i]:
% 1.68/1.91         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 1.68/1.91      inference('cnf', [status(esa)], [t29_mcart_1])).
% 1.68/1.91  thf(t1_subset, axiom,
% 1.68/1.91    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.68/1.91  thf('9', plain,
% 1.68/1.91      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 1.68/1.91      inference('cnf', [status(esa)], [t1_subset])).
% 1.68/1.91  thf('10', plain,
% 1.68/1.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 1.68/1.91      inference('sup-', [status(thm)], ['8', '9'])).
% 1.68/1.91  thf(redefinition_k6_domain_1, axiom,
% 1.68/1.91    (![A:$i,B:$i]:
% 1.68/1.91     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.68/1.91       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.68/1.91  thf('11', plain,
% 1.68/1.91      (![X19 : $i, X20 : $i]:
% 1.68/1.91         ((v1_xboole_0 @ X19)
% 1.68/1.91          | ~ (m1_subset_1 @ X20 @ X19)
% 1.68/1.91          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 1.68/1.91      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.68/1.91  thf('12', plain,
% 1.68/1.91      (![X0 : $i]:
% 1.68/1.91         (((X0) = (k1_xboole_0))
% 1.68/1.91          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.68/1.91          | (v1_xboole_0 @ X0))),
% 1.68/1.91      inference('sup-', [status(thm)], ['10', '11'])).
% 1.68/1.91  thf('13', plain,
% 1.68/1.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.68/1.91      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.68/1.91  thf('14', plain,
% 1.68/1.91      (![X0 : $i]:
% 1.68/1.91         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.68/1.91          | ((X0) = (k1_xboole_0)))),
% 1.68/1.91      inference('clc', [status(thm)], ['12', '13'])).
% 1.68/1.91  thf('15', plain,
% 1.68/1.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 1.68/1.91      inference('sup-', [status(thm)], ['8', '9'])).
% 1.68/1.91  thf(t36_tex_2, axiom,
% 1.68/1.91    (![A:$i]:
% 1.68/1.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.68/1.91       ( ![B:$i]:
% 1.68/1.91         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.68/1.91           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 1.68/1.91  thf('16', plain,
% 1.68/1.91      (![X24 : $i, X25 : $i]:
% 1.68/1.91         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 1.68/1.91          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X25) @ X24) @ X25)
% 1.68/1.91          | ~ (l1_pre_topc @ X25)
% 1.68/1.91          | ~ (v2_pre_topc @ X25)
% 1.68/1.91          | (v2_struct_0 @ X25))),
% 1.68/1.91      inference('cnf', [status(esa)], [t36_tex_2])).
% 1.68/1.91  thf('17', plain,
% 1.68/1.91      (![X0 : $i]:
% 1.68/1.91         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.68/1.91          | (v2_struct_0 @ X0)
% 1.68/1.91          | ~ (v2_pre_topc @ X0)
% 1.68/1.91          | ~ (l1_pre_topc @ X0)
% 1.68/1.91          | (v2_tex_2 @ 
% 1.68/1.91             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 1.68/1.91             X0))),
% 1.68/1.91      inference('sup-', [status(thm)], ['15', '16'])).
% 1.68/1.91  thf('18', plain,
% 1.68/1.91      (![X0 : $i]:
% 1.68/1.91         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.68/1.91          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.68/1.91          | ~ (l1_pre_topc @ X0)
% 1.68/1.91          | ~ (v2_pre_topc @ X0)
% 1.68/1.91          | (v2_struct_0 @ X0)
% 1.68/1.91          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 1.68/1.91      inference('sup+', [status(thm)], ['14', '17'])).
% 1.68/1.91  thf('19', plain,
% 1.68/1.91      (![X0 : $i]:
% 1.68/1.91         ((v2_struct_0 @ X0)
% 1.68/1.91          | ~ (v2_pre_topc @ X0)
% 1.68/1.91          | ~ (l1_pre_topc @ X0)
% 1.68/1.91          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.68/1.91          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 1.68/1.91      inference('simplify', [status(thm)], ['18'])).
% 1.68/1.91  thf('20', plain,
% 1.68/1.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 1.68/1.91      inference('sup-', [status(thm)], ['8', '9'])).
% 1.68/1.91  thf(t55_subset_1, axiom,
% 1.68/1.91    (![A:$i,B:$i]:
% 1.68/1.91     ( ( m1_subset_1 @ B @ A ) =>
% 1.68/1.91       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 1.68/1.91         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.68/1.91  thf('21', plain,
% 1.68/1.91      (![X6 : $i, X7 : $i]:
% 1.68/1.91         (((X6) = (k1_xboole_0))
% 1.68/1.91          | ~ (m1_subset_1 @ X7 @ X6)
% 1.68/1.91          | (m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X6)))),
% 1.68/1.91      inference('cnf', [status(esa)], [t55_subset_1])).
% 1.68/1.91  thf('22', plain,
% 1.68/1.91      (![X0 : $i]:
% 1.68/1.91         (((X0) = (k1_xboole_0))
% 1.68/1.91          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 1.68/1.91          | ((X0) = (k1_xboole_0)))),
% 1.68/1.91      inference('sup-', [status(thm)], ['20', '21'])).
% 1.68/1.91  thf('23', plain,
% 1.68/1.91      (![X0 : $i]:
% 1.68/1.91         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 1.68/1.91          | ((X0) = (k1_xboole_0)))),
% 1.68/1.91      inference('simplify', [status(thm)], ['22'])).
% 1.68/1.91  thf(t4_subset_1, axiom,
% 1.68/1.91    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.68/1.91  thf('24', plain,
% 1.68/1.91      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 1.68/1.91      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.68/1.91  thf(d7_tex_2, axiom,
% 1.68/1.91    (![A:$i]:
% 1.68/1.91     ( ( l1_pre_topc @ A ) =>
% 1.68/1.91       ( ![B:$i]:
% 1.68/1.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.68/1.91           ( ( v3_tex_2 @ B @ A ) <=>
% 1.68/1.91             ( ( v2_tex_2 @ B @ A ) & 
% 1.68/1.91               ( ![C:$i]:
% 1.68/1.91                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.68/1.91                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.68/1.91                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 1.68/1.91  thf('25', plain,
% 1.68/1.91      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.68/1.91         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.68/1.91          | ~ (v3_tex_2 @ X21 @ X22)
% 1.68/1.91          | ~ (v2_tex_2 @ X23 @ X22)
% 1.68/1.91          | ~ (r1_tarski @ X21 @ X23)
% 1.68/1.91          | ((X21) = (X23))
% 1.68/1.91          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.68/1.91          | ~ (l1_pre_topc @ X22))),
% 1.68/1.91      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.68/1.91  thf('26', plain,
% 1.68/1.91      (![X0 : $i, X1 : $i]:
% 1.68/1.91         (~ (l1_pre_topc @ X0)
% 1.68/1.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.68/1.91          | ((k1_xboole_0) = (X1))
% 1.68/1.91          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 1.68/1.91          | ~ (v2_tex_2 @ X1 @ X0)
% 1.68/1.91          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 1.68/1.91      inference('sup-', [status(thm)], ['24', '25'])).
% 1.68/1.91  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.68/1.91  thf('27', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 1.68/1.91      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.68/1.91  thf('28', plain,
% 1.68/1.91      (![X0 : $i, X1 : $i]:
% 1.68/1.91         (~ (l1_pre_topc @ X0)
% 1.68/1.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.68/1.91          | ((k1_xboole_0) = (X1))
% 1.68/1.91          | ~ (v2_tex_2 @ X1 @ X0)
% 1.68/1.91          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 1.68/1.91      inference('demod', [status(thm)], ['26', '27'])).
% 1.68/1.91  thf('29', plain,
% 1.68/1.91      (![X0 : $i]:
% 1.68/1.91         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.68/1.91          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.68/1.91          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.68/1.91          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 1.68/1.91          | ~ (l1_pre_topc @ X0))),
% 1.68/1.91      inference('sup-', [status(thm)], ['23', '28'])).
% 1.68/1.91  thf(t1_boole, axiom,
% 1.68/1.91    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.68/1.91  thf('30', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 1.68/1.91      inference('cnf', [status(esa)], [t1_boole])).
% 1.68/1.91  thf(t49_zfmisc_1, axiom,
% 1.68/1.91    (![A:$i,B:$i]:
% 1.68/1.91     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 1.68/1.91  thf('31', plain,
% 1.68/1.91      (![X3 : $i, X4 : $i]:
% 1.68/1.91         ((k2_xboole_0 @ (k1_tarski @ X3) @ X4) != (k1_xboole_0))),
% 1.68/1.91      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 1.68/1.91  thf('32', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 1.68/1.91      inference('sup-', [status(thm)], ['30', '31'])).
% 1.68/1.91  thf('33', plain,
% 1.68/1.91      (![X0 : $i]:
% 1.68/1.91         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.68/1.91          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.68/1.91          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.68/1.91          | ~ (l1_pre_topc @ X0))),
% 1.68/1.91      inference('simplify_reflect-', [status(thm)], ['29', '32'])).
% 1.68/1.91  thf('34', plain,
% 1.68/1.91      (![X0 : $i]:
% 1.68/1.91         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.68/1.91          | ~ (l1_pre_topc @ X0)
% 1.68/1.91          | ~ (v2_pre_topc @ X0)
% 1.68/1.91          | (v2_struct_0 @ X0)
% 1.68/1.91          | ~ (l1_pre_topc @ X0)
% 1.68/1.91          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.68/1.91          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 1.68/1.91      inference('sup-', [status(thm)], ['19', '33'])).
% 1.68/1.91  thf('35', plain,
% 1.68/1.91      (![X0 : $i]:
% 1.68/1.91         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.68/1.91          | (v2_struct_0 @ X0)
% 1.68/1.91          | ~ (v2_pre_topc @ X0)
% 1.68/1.91          | ~ (l1_pre_topc @ X0)
% 1.68/1.91          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 1.68/1.91      inference('simplify', [status(thm)], ['34'])).
% 1.68/1.91  thf('36', plain,
% 1.68/1.91      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.68/1.91        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.68/1.91        | ~ (l1_pre_topc @ sk_A)
% 1.68/1.91        | ~ (v2_pre_topc @ sk_A)
% 1.68/1.91        | (v2_struct_0 @ sk_A))),
% 1.68/1.91      inference('sup-', [status(thm)], ['7', '35'])).
% 1.68/1.91  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.68/1.91  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.68/1.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.68/1.91  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 1.68/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.91  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 1.68/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.91  thf('40', plain,
% 1.68/1.91      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 1.68/1.91      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 1.68/1.91  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 1.68/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.91  thf('42', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 1.68/1.91      inference('clc', [status(thm)], ['40', '41'])).
% 1.68/1.91  thf(fc2_struct_0, axiom,
% 1.68/1.91    (![A:$i]:
% 1.68/1.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.68/1.91       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.68/1.91  thf('43', plain,
% 1.68/1.91      (![X18 : $i]:
% 1.68/1.91         (~ (v1_xboole_0 @ (u1_struct_0 @ X18))
% 1.68/1.91          | ~ (l1_struct_0 @ X18)
% 1.68/1.91          | (v2_struct_0 @ X18))),
% 1.68/1.91      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.68/1.91  thf('44', plain,
% 1.68/1.91      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.68/1.91        | (v2_struct_0 @ sk_A)
% 1.68/1.91        | ~ (l1_struct_0 @ sk_A))),
% 1.68/1.91      inference('sup-', [status(thm)], ['42', '43'])).
% 1.68/1.91  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.68/1.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.68/1.91  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.68/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.91  thf(dt_l1_pre_topc, axiom,
% 1.68/1.91    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.68/1.91  thf('47', plain,
% 1.68/1.91      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 1.68/1.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.68/1.91  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 1.68/1.91      inference('sup-', [status(thm)], ['46', '47'])).
% 1.68/1.91  thf('49', plain, ((v2_struct_0 @ sk_A)),
% 1.68/1.91      inference('demod', [status(thm)], ['44', '45', '48'])).
% 1.68/1.91  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 1.68/1.91  
% 1.68/1.91  % SZS output end Refutation
% 1.68/1.91  
% 1.68/1.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
