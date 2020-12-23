%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mzIcV6HrfN

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:09 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 106 expanded)
%              Number of leaves         :   35 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  549 ( 810 expanded)
%              Number of equality atoms :   40 (  47 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

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

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

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
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X26 ) @ X25 ) @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X6 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
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

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_tex_2 @ X22 @ X23 )
      | ~ ( v2_tex_2 @ X24 @ X23 )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ( X22 = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['28','31'])).

thf('33',plain,(
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
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','34'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['39','40'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('42',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('43',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('46',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('47',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['43','44','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mzIcV6HrfN
% 0.13/0.36  % Computer   : n001.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 20:04:15 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.36  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.98/1.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.98/1.18  % Solved by: fo/fo7.sh
% 0.98/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.98/1.18  % done 670 iterations in 0.717s
% 0.98/1.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.98/1.18  % SZS output start Refutation
% 0.98/1.18  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.98/1.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.98/1.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.98/1.18  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.98/1.18  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.98/1.18  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.98/1.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.98/1.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.98/1.18  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.98/1.18  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.98/1.18  thf(sk_B_type, type, sk_B: $i > $i).
% 0.98/1.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.98/1.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.98/1.18  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.98/1.18  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.98/1.18  thf(sk_A_type, type, sk_A: $i).
% 0.98/1.18  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.98/1.18  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.98/1.18  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.98/1.18  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.98/1.18  thf(t46_tex_2, conjecture,
% 0.98/1.18    (![A:$i]:
% 0.98/1.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.98/1.18       ( ![B:$i]:
% 0.98/1.18         ( ( ( v1_xboole_0 @ B ) & 
% 0.98/1.18             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.98/1.18           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.98/1.18  thf(zf_stmt_0, negated_conjecture,
% 0.98/1.18    (~( ![A:$i]:
% 0.98/1.18        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.98/1.18            ( l1_pre_topc @ A ) ) =>
% 0.98/1.18          ( ![B:$i]:
% 0.98/1.18            ( ( ( v1_xboole_0 @ B ) & 
% 0.98/1.18                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.98/1.18              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.98/1.18    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.98/1.18  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf(l13_xboole_0, axiom,
% 0.98/1.18    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.98/1.18  thf('1', plain,
% 0.98/1.18      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.98/1.18      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.98/1.18  thf('2', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('3', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('4', plain,
% 0.98/1.18      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.98/1.18      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.98/1.18  thf('5', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['3', '4'])).
% 0.98/1.18  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.98/1.18      inference('demod', [status(thm)], ['2', '5'])).
% 0.98/1.18  thf('7', plain,
% 0.98/1.18      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.98/1.18      inference('sup+', [status(thm)], ['1', '6'])).
% 0.98/1.18  thf(t34_mcart_1, axiom,
% 0.98/1.18    (![A:$i]:
% 0.98/1.18     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.98/1.18          ( ![B:$i]:
% 0.98/1.18            ( ~( ( r2_hidden @ B @ A ) & 
% 0.98/1.18                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.98/1.18                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.98/1.18                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.98/1.18  thf('8', plain,
% 0.98/1.18      (![X13 : $i]:
% 0.98/1.18         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 0.98/1.18      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.98/1.18  thf(t1_subset, axiom,
% 0.98/1.18    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.98/1.18  thf('9', plain,
% 0.98/1.18      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.98/1.18      inference('cnf', [status(esa)], [t1_subset])).
% 0.98/1.18  thf('10', plain,
% 0.98/1.18      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['8', '9'])).
% 0.98/1.18  thf(redefinition_k6_domain_1, axiom,
% 0.98/1.18    (![A:$i,B:$i]:
% 0.98/1.18     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.98/1.18       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.98/1.18  thf('11', plain,
% 0.98/1.18      (![X20 : $i, X21 : $i]:
% 0.98/1.18         ((v1_xboole_0 @ X20)
% 0.98/1.18          | ~ (m1_subset_1 @ X21 @ X20)
% 0.98/1.18          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.98/1.18      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.98/1.18  thf('12', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         (((X0) = (k1_xboole_0))
% 0.98/1.18          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.98/1.18          | (v1_xboole_0 @ X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['10', '11'])).
% 0.98/1.18  thf('13', plain,
% 0.98/1.18      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.98/1.18      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.98/1.18  thf('14', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.98/1.18          | ((X0) = (k1_xboole_0)))),
% 0.98/1.18      inference('clc', [status(thm)], ['12', '13'])).
% 0.98/1.18  thf('15', plain,
% 0.98/1.18      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['8', '9'])).
% 0.98/1.18  thf(t36_tex_2, axiom,
% 0.98/1.18    (![A:$i]:
% 0.98/1.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.98/1.18       ( ![B:$i]:
% 0.98/1.18         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.98/1.18           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.98/1.18  thf('16', plain,
% 0.98/1.18      (![X25 : $i, X26 : $i]:
% 0.98/1.18         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 0.98/1.18          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X26) @ X25) @ X26)
% 0.98/1.18          | ~ (l1_pre_topc @ X26)
% 0.98/1.18          | ~ (v2_pre_topc @ X26)
% 0.98/1.18          | (v2_struct_0 @ X26))),
% 0.98/1.18      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.98/1.18  thf('17', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.98/1.18          | (v2_struct_0 @ X0)
% 0.98/1.18          | ~ (v2_pre_topc @ X0)
% 0.98/1.18          | ~ (l1_pre_topc @ X0)
% 0.98/1.18          | (v2_tex_2 @ 
% 0.98/1.18             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.98/1.18             X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['15', '16'])).
% 0.98/1.18  thf('18', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.98/1.18          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.98/1.18          | ~ (l1_pre_topc @ X0)
% 0.98/1.18          | ~ (v2_pre_topc @ X0)
% 0.98/1.18          | (v2_struct_0 @ X0)
% 0.98/1.18          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 0.98/1.18      inference('sup+', [status(thm)], ['14', '17'])).
% 0.98/1.18  thf('19', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         ((v2_struct_0 @ X0)
% 0.98/1.18          | ~ (v2_pre_topc @ X0)
% 0.98/1.18          | ~ (l1_pre_topc @ X0)
% 0.98/1.18          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.98/1.18          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 0.98/1.18      inference('simplify', [status(thm)], ['18'])).
% 0.98/1.18  thf('20', plain,
% 0.98/1.18      (![X13 : $i]:
% 0.98/1.18         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 0.98/1.18      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.98/1.18  thf(t63_subset_1, axiom,
% 0.98/1.18    (![A:$i,B:$i]:
% 0.98/1.18     ( ( r2_hidden @ A @ B ) =>
% 0.98/1.18       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.98/1.18  thf('21', plain,
% 0.98/1.18      (![X6 : $i, X7 : $i]:
% 0.98/1.18         ((m1_subset_1 @ (k1_tarski @ X6) @ (k1_zfmisc_1 @ X7))
% 0.98/1.18          | ~ (r2_hidden @ X6 @ X7))),
% 0.98/1.18      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.98/1.18  thf('22', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         (((X0) = (k1_xboole_0))
% 0.98/1.18          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['20', '21'])).
% 0.98/1.18  thf(t4_subset_1, axiom,
% 0.98/1.18    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.98/1.18  thf('23', plain,
% 0.98/1.18      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.98/1.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.98/1.18  thf(d7_tex_2, axiom,
% 0.98/1.18    (![A:$i]:
% 0.98/1.18     ( ( l1_pre_topc @ A ) =>
% 0.98/1.18       ( ![B:$i]:
% 0.98/1.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.98/1.18           ( ( v3_tex_2 @ B @ A ) <=>
% 0.98/1.18             ( ( v2_tex_2 @ B @ A ) & 
% 0.98/1.18               ( ![C:$i]:
% 0.98/1.18                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.98/1.18                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.98/1.18                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.98/1.18  thf('24', plain,
% 0.98/1.18      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.98/1.18         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.98/1.18          | ~ (v3_tex_2 @ X22 @ X23)
% 0.98/1.18          | ~ (v2_tex_2 @ X24 @ X23)
% 0.98/1.18          | ~ (r1_tarski @ X22 @ X24)
% 0.98/1.18          | ((X22) = (X24))
% 0.98/1.18          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.98/1.18          | ~ (l1_pre_topc @ X23))),
% 0.98/1.18      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.98/1.18  thf('25', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         (~ (l1_pre_topc @ X0)
% 0.98/1.18          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.98/1.18          | ((k1_xboole_0) = (X1))
% 0.98/1.18          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.98/1.18          | ~ (v2_tex_2 @ X1 @ X0)
% 0.98/1.18          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['23', '24'])).
% 0.98/1.18  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.98/1.18  thf('26', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.98/1.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.98/1.18  thf('27', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         (~ (l1_pre_topc @ X0)
% 0.98/1.18          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.98/1.18          | ((k1_xboole_0) = (X1))
% 0.98/1.18          | ~ (v2_tex_2 @ X1 @ X0)
% 0.98/1.18          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.98/1.18      inference('demod', [status(thm)], ['25', '26'])).
% 0.98/1.18  thf('28', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.98/1.18          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.98/1.18          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.98/1.18          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.98/1.18          | ~ (l1_pre_topc @ X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['22', '27'])).
% 0.98/1.18  thf(t1_boole, axiom,
% 0.98/1.18    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.98/1.18  thf('29', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.98/1.18      inference('cnf', [status(esa)], [t1_boole])).
% 0.98/1.18  thf(t49_zfmisc_1, axiom,
% 0.98/1.18    (![A:$i,B:$i]:
% 0.98/1.18     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.98/1.18  thf('30', plain,
% 0.98/1.18      (![X3 : $i, X4 : $i]:
% 0.98/1.18         ((k2_xboole_0 @ (k1_tarski @ X3) @ X4) != (k1_xboole_0))),
% 0.98/1.18      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.98/1.18  thf('31', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['29', '30'])).
% 0.98/1.18  thf('32', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.98/1.18          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.98/1.18          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.98/1.18          | ~ (l1_pre_topc @ X0))),
% 0.98/1.18      inference('simplify_reflect-', [status(thm)], ['28', '31'])).
% 0.98/1.18  thf('33', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.98/1.18          | ~ (l1_pre_topc @ X0)
% 0.98/1.18          | ~ (v2_pre_topc @ X0)
% 0.98/1.18          | (v2_struct_0 @ X0)
% 0.98/1.18          | ~ (l1_pre_topc @ X0)
% 0.98/1.18          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.98/1.18          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['19', '32'])).
% 0.98/1.18  thf('34', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.98/1.18          | (v2_struct_0 @ X0)
% 0.98/1.18          | ~ (v2_pre_topc @ X0)
% 0.98/1.18          | ~ (l1_pre_topc @ X0)
% 0.98/1.18          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 0.98/1.18      inference('simplify', [status(thm)], ['33'])).
% 0.98/1.18  thf('35', plain,
% 0.98/1.18      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.98/1.18        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.98/1.18        | ~ (l1_pre_topc @ sk_A)
% 0.98/1.18        | ~ (v2_pre_topc @ sk_A)
% 0.98/1.18        | (v2_struct_0 @ sk_A))),
% 0.98/1.18      inference('sup-', [status(thm)], ['7', '34'])).
% 0.98/1.18  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.98/1.18  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.18      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.18  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('39', plain,
% 0.98/1.18      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 0.98/1.18      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.98/1.18  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('41', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.98/1.18      inference('clc', [status(thm)], ['39', '40'])).
% 0.98/1.18  thf(fc2_struct_0, axiom,
% 0.98/1.18    (![A:$i]:
% 0.98/1.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.98/1.18       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.98/1.18  thf('42', plain,
% 0.98/1.18      (![X19 : $i]:
% 0.98/1.18         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.98/1.18          | ~ (l1_struct_0 @ X19)
% 0.98/1.18          | (v2_struct_0 @ X19))),
% 0.98/1.18      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.98/1.18  thf('43', plain,
% 0.98/1.18      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.98/1.18        | (v2_struct_0 @ sk_A)
% 0.98/1.18        | ~ (l1_struct_0 @ sk_A))),
% 0.98/1.18      inference('sup-', [status(thm)], ['41', '42'])).
% 0.98/1.18  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.18      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.18  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf(dt_l1_pre_topc, axiom,
% 0.98/1.18    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.98/1.18  thf('46', plain,
% 0.98/1.18      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.98/1.18      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.98/1.18  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 0.98/1.18      inference('sup-', [status(thm)], ['45', '46'])).
% 0.98/1.18  thf('48', plain, ((v2_struct_0 @ sk_A)),
% 0.98/1.18      inference('demod', [status(thm)], ['43', '44', '47'])).
% 0.98/1.18  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 0.98/1.18  
% 0.98/1.18  % SZS output end Refutation
% 0.98/1.18  
% 1.02/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
