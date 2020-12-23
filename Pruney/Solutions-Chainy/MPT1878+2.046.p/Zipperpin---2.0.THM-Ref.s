%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.44zWn7odda

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:09 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 106 expanded)
%              Number of leaves         :   35 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  547 ( 804 expanded)
%              Number of equality atoms :   40 (  47 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

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
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
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
    inference(cnf,[status(esa)],[t9_mcart_1])).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_tex_2 @ X20 @ X21 )
      | ~ ( v2_tex_2 @ X22 @ X21 )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( X20 = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
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
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.44zWn7odda
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:23:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.19/1.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.19/1.46  % Solved by: fo/fo7.sh
% 1.19/1.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.46  % done 763 iterations in 1.004s
% 1.19/1.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.19/1.46  % SZS output start Refutation
% 1.19/1.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.19/1.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.19/1.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.19/1.46  thf(sk_B_type, type, sk_B: $i > $i).
% 1.19/1.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.19/1.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.19/1.46  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.19/1.46  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.19/1.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.19/1.46  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.19/1.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.19/1.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.19/1.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.19/1.46  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 1.19/1.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.19/1.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.19/1.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.19/1.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.19/1.46  thf(t46_tex_2, conjecture,
% 1.19/1.46    (![A:$i]:
% 1.19/1.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.46       ( ![B:$i]:
% 1.19/1.46         ( ( ( v1_xboole_0 @ B ) & 
% 1.19/1.46             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.19/1.46           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 1.19/1.46  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.46    (~( ![A:$i]:
% 1.19/1.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.19/1.46            ( l1_pre_topc @ A ) ) =>
% 1.19/1.46          ( ![B:$i]:
% 1.19/1.46            ( ( ( v1_xboole_0 @ B ) & 
% 1.19/1.46                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.19/1.46              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 1.19/1.46    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 1.19/1.46  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.19/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.46  thf(l13_xboole_0, axiom,
% 1.19/1.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.19/1.46  thf('1', plain,
% 1.19/1.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.19/1.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.19/1.46  thf('2', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 1.19/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.46  thf('3', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.19/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.46  thf('4', plain,
% 1.19/1.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.19/1.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.19/1.46  thf('5', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.19/1.46      inference('sup-', [status(thm)], ['3', '4'])).
% 1.19/1.46  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.19/1.46      inference('demod', [status(thm)], ['2', '5'])).
% 1.19/1.46  thf('7', plain,
% 1.19/1.46      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 1.19/1.46      inference('sup+', [status(thm)], ['1', '6'])).
% 1.19/1.46  thf(t9_mcart_1, axiom,
% 1.19/1.46    (![A:$i]:
% 1.19/1.46     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.19/1.46          ( ![B:$i]:
% 1.19/1.46            ( ~( ( r2_hidden @ B @ A ) & 
% 1.19/1.46                 ( ![C:$i,D:$i]:
% 1.19/1.46                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 1.19/1.46                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 1.19/1.46  thf('8', plain,
% 1.19/1.46      (![X13 : $i]:
% 1.19/1.46         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 1.19/1.46      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.19/1.46  thf(t1_subset, axiom,
% 1.19/1.46    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.19/1.46  thf('9', plain,
% 1.19/1.46      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 1.19/1.46      inference('cnf', [status(esa)], [t1_subset])).
% 1.19/1.46  thf('10', plain,
% 1.19/1.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 1.19/1.46      inference('sup-', [status(thm)], ['8', '9'])).
% 1.19/1.46  thf(redefinition_k6_domain_1, axiom,
% 1.19/1.46    (![A:$i,B:$i]:
% 1.19/1.46     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.19/1.46       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.19/1.46  thf('11', plain,
% 1.19/1.46      (![X18 : $i, X19 : $i]:
% 1.19/1.46         ((v1_xboole_0 @ X18)
% 1.19/1.46          | ~ (m1_subset_1 @ X19 @ X18)
% 1.19/1.46          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 1.19/1.46      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.19/1.46  thf('12', plain,
% 1.19/1.46      (![X0 : $i]:
% 1.19/1.46         (((X0) = (k1_xboole_0))
% 1.19/1.46          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.19/1.46          | (v1_xboole_0 @ X0))),
% 1.19/1.46      inference('sup-', [status(thm)], ['10', '11'])).
% 1.19/1.46  thf('13', plain,
% 1.19/1.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.19/1.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.19/1.46  thf('14', plain,
% 1.19/1.46      (![X0 : $i]:
% 1.19/1.46         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.19/1.46          | ((X0) = (k1_xboole_0)))),
% 1.19/1.46      inference('clc', [status(thm)], ['12', '13'])).
% 1.19/1.46  thf('15', plain,
% 1.19/1.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 1.19/1.46      inference('sup-', [status(thm)], ['8', '9'])).
% 1.19/1.46  thf(t36_tex_2, axiom,
% 1.19/1.46    (![A:$i]:
% 1.19/1.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.46       ( ![B:$i]:
% 1.19/1.46         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.19/1.46           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 1.19/1.46  thf('16', plain,
% 1.19/1.46      (![X23 : $i, X24 : $i]:
% 1.19/1.46         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 1.19/1.46          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 1.19/1.46          | ~ (l1_pre_topc @ X24)
% 1.19/1.46          | ~ (v2_pre_topc @ X24)
% 1.19/1.46          | (v2_struct_0 @ X24))),
% 1.19/1.46      inference('cnf', [status(esa)], [t36_tex_2])).
% 1.19/1.46  thf('17', plain,
% 1.19/1.46      (![X0 : $i]:
% 1.19/1.46         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.19/1.46          | (v2_struct_0 @ X0)
% 1.19/1.46          | ~ (v2_pre_topc @ X0)
% 1.19/1.46          | ~ (l1_pre_topc @ X0)
% 1.19/1.46          | (v2_tex_2 @ 
% 1.19/1.46             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 1.19/1.46             X0))),
% 1.19/1.46      inference('sup-', [status(thm)], ['15', '16'])).
% 1.19/1.46  thf('18', plain,
% 1.19/1.46      (![X0 : $i]:
% 1.19/1.46         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.19/1.46          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.19/1.46          | ~ (l1_pre_topc @ X0)
% 1.19/1.46          | ~ (v2_pre_topc @ X0)
% 1.19/1.46          | (v2_struct_0 @ X0)
% 1.19/1.46          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 1.19/1.46      inference('sup+', [status(thm)], ['14', '17'])).
% 1.19/1.46  thf('19', plain,
% 1.19/1.46      (![X0 : $i]:
% 1.19/1.46         ((v2_struct_0 @ X0)
% 1.19/1.46          | ~ (v2_pre_topc @ X0)
% 1.19/1.46          | ~ (l1_pre_topc @ X0)
% 1.19/1.46          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.19/1.46          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 1.19/1.46      inference('simplify', [status(thm)], ['18'])).
% 1.19/1.46  thf('20', plain,
% 1.19/1.46      (![X13 : $i]:
% 1.19/1.46         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 1.19/1.46      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.19/1.46  thf(t63_subset_1, axiom,
% 1.19/1.46    (![A:$i,B:$i]:
% 1.19/1.46     ( ( r2_hidden @ A @ B ) =>
% 1.19/1.46       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.19/1.46  thf('21', plain,
% 1.19/1.46      (![X6 : $i, X7 : $i]:
% 1.19/1.46         ((m1_subset_1 @ (k1_tarski @ X6) @ (k1_zfmisc_1 @ X7))
% 1.19/1.46          | ~ (r2_hidden @ X6 @ X7))),
% 1.19/1.46      inference('cnf', [status(esa)], [t63_subset_1])).
% 1.19/1.46  thf('22', plain,
% 1.19/1.46      (![X0 : $i]:
% 1.19/1.46         (((X0) = (k1_xboole_0))
% 1.19/1.46          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 1.19/1.46      inference('sup-', [status(thm)], ['20', '21'])).
% 1.19/1.46  thf(t4_subset_1, axiom,
% 1.19/1.46    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.19/1.46  thf('23', plain,
% 1.19/1.46      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 1.19/1.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.19/1.46  thf(d7_tex_2, axiom,
% 1.19/1.46    (![A:$i]:
% 1.19/1.46     ( ( l1_pre_topc @ A ) =>
% 1.19/1.46       ( ![B:$i]:
% 1.19/1.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.46           ( ( v3_tex_2 @ B @ A ) <=>
% 1.19/1.46             ( ( v2_tex_2 @ B @ A ) & 
% 1.19/1.46               ( ![C:$i]:
% 1.19/1.46                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.46                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.19/1.46                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 1.19/1.46  thf('24', plain,
% 1.19/1.46      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.19/1.46         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.19/1.46          | ~ (v3_tex_2 @ X20 @ X21)
% 1.19/1.46          | ~ (v2_tex_2 @ X22 @ X21)
% 1.19/1.46          | ~ (r1_tarski @ X20 @ X22)
% 1.19/1.46          | ((X20) = (X22))
% 1.19/1.46          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.19/1.46          | ~ (l1_pre_topc @ X21))),
% 1.19/1.46      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.19/1.46  thf('25', plain,
% 1.19/1.46      (![X0 : $i, X1 : $i]:
% 1.19/1.46         (~ (l1_pre_topc @ X0)
% 1.19/1.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.19/1.46          | ((k1_xboole_0) = (X1))
% 1.19/1.46          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 1.19/1.46          | ~ (v2_tex_2 @ X1 @ X0)
% 1.19/1.46          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 1.19/1.46      inference('sup-', [status(thm)], ['23', '24'])).
% 1.19/1.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.19/1.46  thf('26', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 1.19/1.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.19/1.46  thf('27', plain,
% 1.19/1.46      (![X0 : $i, X1 : $i]:
% 1.19/1.46         (~ (l1_pre_topc @ X0)
% 1.19/1.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.19/1.46          | ((k1_xboole_0) = (X1))
% 1.19/1.46          | ~ (v2_tex_2 @ X1 @ X0)
% 1.19/1.46          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 1.19/1.46      inference('demod', [status(thm)], ['25', '26'])).
% 1.19/1.46  thf('28', plain,
% 1.19/1.46      (![X0 : $i]:
% 1.19/1.46         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.19/1.46          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.19/1.46          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.19/1.46          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 1.19/1.46          | ~ (l1_pre_topc @ X0))),
% 1.19/1.46      inference('sup-', [status(thm)], ['22', '27'])).
% 1.19/1.46  thf(t1_boole, axiom,
% 1.19/1.46    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.19/1.46  thf('29', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 1.19/1.46      inference('cnf', [status(esa)], [t1_boole])).
% 1.19/1.46  thf(t49_zfmisc_1, axiom,
% 1.19/1.46    (![A:$i,B:$i]:
% 1.19/1.46     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 1.19/1.46  thf('30', plain,
% 1.19/1.46      (![X3 : $i, X4 : $i]:
% 1.19/1.46         ((k2_xboole_0 @ (k1_tarski @ X3) @ X4) != (k1_xboole_0))),
% 1.19/1.46      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 1.19/1.46  thf('31', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 1.19/1.46      inference('sup-', [status(thm)], ['29', '30'])).
% 1.19/1.46  thf('32', plain,
% 1.19/1.46      (![X0 : $i]:
% 1.19/1.46         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.19/1.46          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.19/1.46          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.19/1.46          | ~ (l1_pre_topc @ X0))),
% 1.19/1.46      inference('simplify_reflect-', [status(thm)], ['28', '31'])).
% 1.19/1.46  thf('33', plain,
% 1.19/1.46      (![X0 : $i]:
% 1.19/1.46         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.19/1.46          | ~ (l1_pre_topc @ X0)
% 1.19/1.46          | ~ (v2_pre_topc @ X0)
% 1.19/1.46          | (v2_struct_0 @ X0)
% 1.19/1.46          | ~ (l1_pre_topc @ X0)
% 1.19/1.46          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.19/1.46          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 1.19/1.46      inference('sup-', [status(thm)], ['19', '32'])).
% 1.19/1.46  thf('34', plain,
% 1.19/1.46      (![X0 : $i]:
% 1.19/1.46         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.19/1.46          | (v2_struct_0 @ X0)
% 1.19/1.46          | ~ (v2_pre_topc @ X0)
% 1.19/1.46          | ~ (l1_pre_topc @ X0)
% 1.19/1.46          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 1.19/1.46      inference('simplify', [status(thm)], ['33'])).
% 1.19/1.46  thf('35', plain,
% 1.19/1.46      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.19/1.46        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.19/1.46        | ~ (l1_pre_topc @ sk_A)
% 1.19/1.46        | ~ (v2_pre_topc @ sk_A)
% 1.19/1.46        | (v2_struct_0 @ sk_A))),
% 1.19/1.46      inference('sup-', [status(thm)], ['7', '34'])).
% 1.19/1.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.19/1.46  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.19/1.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.19/1.46  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.46  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.46  thf('39', plain,
% 1.19/1.46      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 1.19/1.46      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 1.19/1.46  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 1.19/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.46  thf('41', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 1.19/1.46      inference('clc', [status(thm)], ['39', '40'])).
% 1.19/1.46  thf(fc2_struct_0, axiom,
% 1.19/1.46    (![A:$i]:
% 1.19/1.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.19/1.46       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.19/1.46  thf('42', plain,
% 1.19/1.46      (![X17 : $i]:
% 1.19/1.46         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 1.19/1.46          | ~ (l1_struct_0 @ X17)
% 1.19/1.46          | (v2_struct_0 @ X17))),
% 1.19/1.46      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.19/1.46  thf('43', plain,
% 1.19/1.46      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.19/1.46        | (v2_struct_0 @ sk_A)
% 1.19/1.46        | ~ (l1_struct_0 @ sk_A))),
% 1.19/1.46      inference('sup-', [status(thm)], ['41', '42'])).
% 1.19/1.46  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.19/1.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.19/1.46  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.46  thf(dt_l1_pre_topc, axiom,
% 1.19/1.46    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.19/1.46  thf('46', plain,
% 1.19/1.46      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 1.19/1.46      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.19/1.46  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 1.19/1.46      inference('sup-', [status(thm)], ['45', '46'])).
% 1.19/1.46  thf('48', plain, ((v2_struct_0 @ sk_A)),
% 1.19/1.46      inference('demod', [status(thm)], ['43', '44', '47'])).
% 1.19/1.46  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 1.19/1.46  
% 1.19/1.46  % SZS output end Refutation
% 1.19/1.46  
% 1.33/1.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
