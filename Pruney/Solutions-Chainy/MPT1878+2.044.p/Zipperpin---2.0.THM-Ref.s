%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XlfD3pcBso

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:09 EST 2020

% Result     : Theorem 2.48s
% Output     : Refutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 109 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  554 ( 808 expanded)
%              Number of equality atoms :   43 (  49 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
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

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_tex_2 @ X18 @ X19 )
      | ~ ( v2_tex_2 @ X20 @ X19 )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( X18 = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
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
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ X5 )
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
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
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
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XlfD3pcBso
% 0.11/0.33  % Computer   : n001.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 13:08:30 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 2.48/2.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.48/2.65  % Solved by: fo/fo7.sh
% 2.48/2.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.48/2.65  % done 1616 iterations in 2.233s
% 2.48/2.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.48/2.65  % SZS output start Refutation
% 2.48/2.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.48/2.65  thf(sk_A_type, type, sk_A: $i).
% 2.48/2.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.48/2.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.48/2.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.48/2.65  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 2.48/2.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.48/2.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.48/2.65  thf(sk_B_type, type, sk_B: $i > $i).
% 2.48/2.65  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 2.48/2.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.48/2.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.48/2.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.48/2.65  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 2.48/2.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.48/2.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.48/2.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.48/2.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.48/2.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.48/2.65  thf(t46_tex_2, conjecture,
% 2.48/2.65    (![A:$i]:
% 2.48/2.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.48/2.65       ( ![B:$i]:
% 2.48/2.65         ( ( ( v1_xboole_0 @ B ) & 
% 2.48/2.65             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.48/2.65           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 2.48/2.65  thf(zf_stmt_0, negated_conjecture,
% 2.48/2.65    (~( ![A:$i]:
% 2.48/2.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.48/2.65            ( l1_pre_topc @ A ) ) =>
% 2.48/2.65          ( ![B:$i]:
% 2.48/2.65            ( ( ( v1_xboole_0 @ B ) & 
% 2.48/2.65                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.48/2.65              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 2.48/2.65    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 2.48/2.65  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 2.48/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.65  thf(l13_xboole_0, axiom,
% 2.48/2.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.48/2.65  thf('1', plain,
% 2.48/2.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.48/2.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.48/2.65  thf('2', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 2.48/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.65  thf('3', plain, ((v1_xboole_0 @ sk_B_1)),
% 2.48/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.65  thf('4', plain,
% 2.48/2.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.48/2.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.48/2.65  thf('5', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.48/2.65      inference('sup-', [status(thm)], ['3', '4'])).
% 2.48/2.65  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 2.48/2.65      inference('demod', [status(thm)], ['2', '5'])).
% 2.48/2.65  thf('7', plain,
% 2.48/2.65      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 2.48/2.65      inference('sup+', [status(thm)], ['1', '6'])).
% 2.48/2.65  thf(t7_xboole_0, axiom,
% 2.48/2.65    (![A:$i]:
% 2.48/2.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.48/2.65          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.48/2.65  thf('8', plain,
% 2.48/2.65      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 2.48/2.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.48/2.65  thf(t1_subset, axiom,
% 2.48/2.65    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 2.48/2.65  thf('9', plain,
% 2.48/2.65      (![X9 : $i, X10 : $i]:
% 2.48/2.65         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 2.48/2.65      inference('cnf', [status(esa)], [t1_subset])).
% 2.48/2.65  thf('10', plain,
% 2.48/2.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 2.48/2.65      inference('sup-', [status(thm)], ['8', '9'])).
% 2.48/2.65  thf(redefinition_k6_domain_1, axiom,
% 2.48/2.65    (![A:$i,B:$i]:
% 2.48/2.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 2.48/2.65       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 2.48/2.65  thf('11', plain,
% 2.48/2.65      (![X16 : $i, X17 : $i]:
% 2.48/2.65         ((v1_xboole_0 @ X16)
% 2.48/2.65          | ~ (m1_subset_1 @ X17 @ X16)
% 2.48/2.65          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 2.48/2.65      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 2.48/2.65  thf('12', plain,
% 2.48/2.65      (![X0 : $i]:
% 2.48/2.65         (((X0) = (k1_xboole_0))
% 2.48/2.65          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 2.48/2.65          | (v1_xboole_0 @ X0))),
% 2.48/2.65      inference('sup-', [status(thm)], ['10', '11'])).
% 2.48/2.65  thf('13', plain,
% 2.48/2.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.48/2.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.48/2.65  thf('14', plain,
% 2.48/2.65      (![X0 : $i]:
% 2.48/2.65         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 2.48/2.65          | ((X0) = (k1_xboole_0)))),
% 2.48/2.65      inference('clc', [status(thm)], ['12', '13'])).
% 2.48/2.65  thf('15', plain,
% 2.48/2.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 2.48/2.65      inference('sup-', [status(thm)], ['8', '9'])).
% 2.48/2.65  thf(t36_tex_2, axiom,
% 2.48/2.65    (![A:$i]:
% 2.48/2.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.48/2.65       ( ![B:$i]:
% 2.48/2.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.48/2.65           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 2.48/2.65  thf('16', plain,
% 2.48/2.65      (![X21 : $i, X22 : $i]:
% 2.48/2.65         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 2.48/2.65          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X22) @ X21) @ X22)
% 2.48/2.65          | ~ (l1_pre_topc @ X22)
% 2.48/2.65          | ~ (v2_pre_topc @ X22)
% 2.48/2.65          | (v2_struct_0 @ X22))),
% 2.48/2.65      inference('cnf', [status(esa)], [t36_tex_2])).
% 2.48/2.65  thf('17', plain,
% 2.48/2.65      (![X0 : $i]:
% 2.48/2.65         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 2.48/2.65          | (v2_struct_0 @ X0)
% 2.48/2.65          | ~ (v2_pre_topc @ X0)
% 2.48/2.65          | ~ (l1_pre_topc @ X0)
% 2.48/2.65          | (v2_tex_2 @ 
% 2.48/2.65             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 2.48/2.65             X0))),
% 2.48/2.65      inference('sup-', [status(thm)], ['15', '16'])).
% 2.48/2.65  thf('18', plain,
% 2.48/2.65      (![X0 : $i]:
% 2.48/2.65         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 2.48/2.65          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 2.48/2.65          | ~ (l1_pre_topc @ X0)
% 2.48/2.65          | ~ (v2_pre_topc @ X0)
% 2.48/2.65          | (v2_struct_0 @ X0)
% 2.48/2.65          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 2.48/2.65      inference('sup+', [status(thm)], ['14', '17'])).
% 2.48/2.65  thf('19', plain,
% 2.48/2.65      (![X0 : $i]:
% 2.48/2.65         ((v2_struct_0 @ X0)
% 2.48/2.65          | ~ (v2_pre_topc @ X0)
% 2.48/2.65          | ~ (l1_pre_topc @ X0)
% 2.48/2.65          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 2.48/2.65          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 2.48/2.65      inference('simplify', [status(thm)], ['18'])).
% 2.48/2.65  thf('20', plain,
% 2.48/2.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 2.48/2.65      inference('sup-', [status(thm)], ['8', '9'])).
% 2.48/2.65  thf(t55_subset_1, axiom,
% 2.48/2.65    (![A:$i,B:$i]:
% 2.48/2.65     ( ( m1_subset_1 @ B @ A ) =>
% 2.48/2.65       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 2.48/2.65         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 2.48/2.65  thf('21', plain,
% 2.48/2.65      (![X7 : $i, X8 : $i]:
% 2.48/2.65         (((X7) = (k1_xboole_0))
% 2.48/2.65          | ~ (m1_subset_1 @ X8 @ X7)
% 2.48/2.65          | (m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X7)))),
% 2.48/2.65      inference('cnf', [status(esa)], [t55_subset_1])).
% 2.48/2.65  thf('22', plain,
% 2.48/2.65      (![X0 : $i]:
% 2.48/2.65         (((X0) = (k1_xboole_0))
% 2.48/2.65          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 2.48/2.65          | ((X0) = (k1_xboole_0)))),
% 2.48/2.65      inference('sup-', [status(thm)], ['20', '21'])).
% 2.48/2.65  thf('23', plain,
% 2.48/2.65      (![X0 : $i]:
% 2.48/2.65         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 2.48/2.65          | ((X0) = (k1_xboole_0)))),
% 2.48/2.65      inference('simplify', [status(thm)], ['22'])).
% 2.48/2.65  thf(t4_subset_1, axiom,
% 2.48/2.65    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.48/2.65  thf('24', plain,
% 2.48/2.65      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 2.48/2.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.48/2.65  thf(d7_tex_2, axiom,
% 2.48/2.65    (![A:$i]:
% 2.48/2.65     ( ( l1_pre_topc @ A ) =>
% 2.48/2.65       ( ![B:$i]:
% 2.48/2.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.48/2.65           ( ( v3_tex_2 @ B @ A ) <=>
% 2.48/2.65             ( ( v2_tex_2 @ B @ A ) & 
% 2.48/2.65               ( ![C:$i]:
% 2.48/2.65                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.48/2.65                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 2.48/2.65                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 2.48/2.65  thf('25', plain,
% 2.48/2.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.48/2.65         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 2.48/2.65          | ~ (v3_tex_2 @ X18 @ X19)
% 2.48/2.65          | ~ (v2_tex_2 @ X20 @ X19)
% 2.48/2.65          | ~ (r1_tarski @ X18 @ X20)
% 2.48/2.65          | ((X18) = (X20))
% 2.48/2.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 2.48/2.65          | ~ (l1_pre_topc @ X19))),
% 2.48/2.65      inference('cnf', [status(esa)], [d7_tex_2])).
% 2.48/2.65  thf('26', plain,
% 2.48/2.65      (![X0 : $i, X1 : $i]:
% 2.48/2.65         (~ (l1_pre_topc @ X0)
% 2.48/2.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.48/2.65          | ((k1_xboole_0) = (X1))
% 2.48/2.65          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 2.48/2.65          | ~ (v2_tex_2 @ X1 @ X0)
% 2.48/2.65          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 2.48/2.65      inference('sup-', [status(thm)], ['24', '25'])).
% 2.48/2.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.48/2.65  thf('27', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 2.48/2.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.48/2.65  thf('28', plain,
% 2.48/2.65      (![X0 : $i, X1 : $i]:
% 2.48/2.65         (~ (l1_pre_topc @ X0)
% 2.48/2.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.48/2.65          | ((k1_xboole_0) = (X1))
% 2.48/2.65          | ~ (v2_tex_2 @ X1 @ X0)
% 2.48/2.65          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 2.48/2.65      inference('demod', [status(thm)], ['26', '27'])).
% 2.48/2.65  thf('29', plain,
% 2.48/2.65      (![X0 : $i]:
% 2.48/2.65         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 2.48/2.65          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 2.48/2.65          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 2.48/2.65          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 2.48/2.65          | ~ (l1_pre_topc @ X0))),
% 2.48/2.65      inference('sup-', [status(thm)], ['23', '28'])).
% 2.48/2.65  thf(t1_boole, axiom,
% 2.48/2.65    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.48/2.65  thf('30', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 2.48/2.65      inference('cnf', [status(esa)], [t1_boole])).
% 2.48/2.65  thf(t49_zfmisc_1, axiom,
% 2.48/2.65    (![A:$i,B:$i]:
% 2.48/2.65     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 2.48/2.65  thf('31', plain,
% 2.48/2.65      (![X4 : $i, X5 : $i]:
% 2.48/2.65         ((k2_xboole_0 @ (k1_tarski @ X4) @ X5) != (k1_xboole_0))),
% 2.48/2.65      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 2.48/2.65  thf('32', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 2.48/2.65      inference('sup-', [status(thm)], ['30', '31'])).
% 2.48/2.65  thf('33', plain,
% 2.48/2.65      (![X0 : $i]:
% 2.48/2.65         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 2.48/2.65          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 2.48/2.65          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 2.48/2.65          | ~ (l1_pre_topc @ X0))),
% 2.48/2.65      inference('simplify_reflect-', [status(thm)], ['29', '32'])).
% 2.48/2.65  thf('34', plain,
% 2.48/2.65      (![X0 : $i]:
% 2.48/2.65         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 2.48/2.65          | ~ (l1_pre_topc @ X0)
% 2.48/2.65          | ~ (v2_pre_topc @ X0)
% 2.48/2.65          | (v2_struct_0 @ X0)
% 2.48/2.65          | ~ (l1_pre_topc @ X0)
% 2.48/2.65          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 2.48/2.65          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 2.48/2.65      inference('sup-', [status(thm)], ['19', '33'])).
% 2.48/2.65  thf('35', plain,
% 2.48/2.65      (![X0 : $i]:
% 2.48/2.65         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 2.48/2.65          | (v2_struct_0 @ X0)
% 2.48/2.65          | ~ (v2_pre_topc @ X0)
% 2.48/2.65          | ~ (l1_pre_topc @ X0)
% 2.48/2.65          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 2.48/2.65      inference('simplify', [status(thm)], ['34'])).
% 2.48/2.65  thf('36', plain,
% 2.48/2.65      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.48/2.65        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 2.48/2.65        | ~ (l1_pre_topc @ sk_A)
% 2.48/2.65        | ~ (v2_pre_topc @ sk_A)
% 2.48/2.65        | (v2_struct_0 @ sk_A))),
% 2.48/2.65      inference('sup-', [status(thm)], ['7', '35'])).
% 2.48/2.65  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.48/2.65  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.48/2.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.48/2.65  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 2.48/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.65  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 2.48/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.65  thf('40', plain,
% 2.48/2.65      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 2.48/2.65      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 2.48/2.65  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 2.48/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.65  thf('42', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 2.48/2.65      inference('clc', [status(thm)], ['40', '41'])).
% 2.48/2.65  thf(fc2_struct_0, axiom,
% 2.48/2.65    (![A:$i]:
% 2.48/2.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.48/2.65       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.48/2.65  thf('43', plain,
% 2.48/2.65      (![X15 : $i]:
% 2.48/2.65         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 2.48/2.65          | ~ (l1_struct_0 @ X15)
% 2.48/2.65          | (v2_struct_0 @ X15))),
% 2.48/2.65      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.48/2.65  thf('44', plain,
% 2.48/2.65      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.48/2.65        | (v2_struct_0 @ sk_A)
% 2.48/2.65        | ~ (l1_struct_0 @ sk_A))),
% 2.48/2.65      inference('sup-', [status(thm)], ['42', '43'])).
% 2.48/2.65  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.48/2.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.48/2.65  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 2.48/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.65  thf(dt_l1_pre_topc, axiom,
% 2.48/2.65    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.48/2.65  thf('47', plain,
% 2.48/2.65      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 2.48/2.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.48/2.65  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 2.48/2.65      inference('sup-', [status(thm)], ['46', '47'])).
% 2.48/2.65  thf('49', plain, ((v2_struct_0 @ sk_A)),
% 2.48/2.65      inference('demod', [status(thm)], ['44', '45', '48'])).
% 2.48/2.65  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 2.48/2.65  
% 2.48/2.65  % SZS output end Refutation
% 2.48/2.65  
% 2.48/2.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
