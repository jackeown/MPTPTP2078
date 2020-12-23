%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A9md045cP6

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:34 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 144 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :   17
%              Number of atoms          :  395 (1023 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X16 ) @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_zfmisc_1 @ X24 )
      | ( X25 = X24 )
      | ~ ( r1_tarski @ X25 @ X24 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( ( sk_B_1 @ X0 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('5',plain,(
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('10',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_zfmisc_1 @ X24 )
      | ( X25 = X24 )
      | ~ ( r1_tarski @ X25 @ X24 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( ( k1_tarski @ sk_B_2 )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( ( k1_tarski @ sk_B_2 )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X13: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k1_tarski @ sk_B_2 )
      = sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k1_tarski @ sk_B_2 )
    = sk_A ),
    inference(clc,[status(thm)],['23','24'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(cc2_subset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_subset_1 @ B @ A )
           => ~ ( v1_xboole_0 @ B ) ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( v1_xboole_0 @ X14 )
      | ( v1_subset_1 @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_subset_1 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_subset_1 @ X1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X13: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_subset_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X16: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( sk_B_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( sk_B_1 @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','38'])).

thf('40',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( sk_B_1 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_B_1 @ sk_A )
    = sk_A ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X16: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('45',plain,(
    ~ ( v1_subset_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('48',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_tarski @ sk_B_2 )
    = sk_A ),
    inference(clc,[status(thm)],['23','24'])).

thf('50',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['45','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A9md045cP6
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:02:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 221 iterations in 0.137s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.60  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.42/0.60  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.42/0.60  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.42/0.60  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.60  thf(rc3_subset_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ?[B:$i]:
% 0.42/0.60       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.42/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      (![X16 : $i]: (m1_subset_1 @ (sk_B_1 @ X16) @ (k1_zfmisc_1 @ X16))),
% 0.42/0.60      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.42/0.60  thf(t3_subset, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      (![X17 : $i, X18 : $i]:
% 0.42/0.60         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.60  thf('2', plain, (![X0 : $i]: (r1_tarski @ (sk_B_1 @ X0) @ X0)),
% 0.42/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.60  thf(t1_tex_2, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.42/0.60           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (![X24 : $i, X25 : $i]:
% 0.42/0.60         ((v1_xboole_0 @ X24)
% 0.42/0.60          | ~ (v1_zfmisc_1 @ X24)
% 0.42/0.60          | ((X25) = (X24))
% 0.42/0.60          | ~ (r1_tarski @ X25 @ X24)
% 0.42/0.60          | (v1_xboole_0 @ X25))),
% 0.42/0.60      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.42/0.60          | ((sk_B_1 @ X0) = (X0))
% 0.42/0.60          | ~ (v1_zfmisc_1 @ X0)
% 0.42/0.60          | (v1_xboole_0 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.60  thf(t6_tex_2, conjecture,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( m1_subset_1 @ B @ A ) =>
% 0.42/0.60           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.42/0.60                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i]:
% 0.42/0.60        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.60          ( ![B:$i]:
% 0.42/0.60            ( ( m1_subset_1 @ B @ A ) =>
% 0.42/0.60              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.42/0.60                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.42/0.60  thf('5', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(dt_k6_domain_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.42/0.60       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (![X20 : $i, X21 : $i]:
% 0.42/0.60         ((v1_xboole_0 @ X20)
% 0.42/0.60          | ~ (m1_subset_1 @ X21 @ X20)
% 0.42/0.60          | (m1_subset_1 @ (k6_domain_1 @ X20 @ X21) @ (k1_zfmisc_1 @ X20)))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.60        | (v1_xboole_0 @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.60  thf('8', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(redefinition_k6_domain_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.42/0.60       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X22 : $i, X23 : $i]:
% 0.42/0.60         ((v1_xboole_0 @ X22)
% 0.42/0.60          | ~ (m1_subset_1 @ X23 @ X22)
% 0.42/0.60          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 0.42/0.60      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      ((((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.42/0.60        | (v1_xboole_0 @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.60  thf('11', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('12', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 0.42/0.60      inference('clc', [status(thm)], ['10', '11'])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (((m1_subset_1 @ (k1_tarski @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.60        | (v1_xboole_0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['7', '12'])).
% 0.42/0.60  thf('14', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      ((m1_subset_1 @ (k1_tarski @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.60      inference('clc', [status(thm)], ['13', '14'])).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (![X17 : $i, X18 : $i]:
% 0.42/0.60         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.60  thf('17', plain, ((r1_tarski @ (k1_tarski @ sk_B_2) @ sk_A)),
% 0.42/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      (![X24 : $i, X25 : $i]:
% 0.42/0.60         ((v1_xboole_0 @ X24)
% 0.42/0.60          | ~ (v1_zfmisc_1 @ X24)
% 0.42/0.60          | ((X25) = (X24))
% 0.42/0.60          | ~ (r1_tarski @ X25 @ X24)
% 0.42/0.60          | (v1_xboole_0 @ X25))),
% 0.42/0.60      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.42/0.60        | ((k1_tarski @ sk_B_2) = (sk_A))
% 0.42/0.60        | ~ (v1_zfmisc_1 @ sk_A)
% 0.42/0.60        | (v1_xboole_0 @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.42/0.60  thf('20', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.42/0.60        | ((k1_tarski @ sk_B_2) = (sk_A))
% 0.42/0.60        | (v1_xboole_0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['19', '20'])).
% 0.42/0.60  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.42/0.60  thf('22', plain, (![X13 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X13))),
% 0.42/0.60      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.42/0.60  thf('23', plain, (((v1_xboole_0 @ sk_A) | ((k1_tarski @ sk_B_2) = (sk_A)))),
% 0.42/0.60      inference('clc', [status(thm)], ['21', '22'])).
% 0.42/0.60  thf('24', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('25', plain, (((k1_tarski @ sk_B_2) = (sk_A))),
% 0.42/0.60      inference('clc', [status(thm)], ['23', '24'])).
% 0.42/0.60  thf(d3_tarski, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.42/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.42/0.60  thf('26', plain,
% 0.42/0.60      (![X4 : $i, X6 : $i]:
% 0.42/0.60         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.42/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.60  thf(d1_xboole_0, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.60  thf('28', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.42/0.60  thf('29', plain,
% 0.42/0.60      (![X17 : $i, X19 : $i]:
% 0.42/0.60         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.42/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.42/0.60  thf(cc2_subset_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.60           ( ( ~( v1_subset_1 @ B @ A ) ) => ( ~( v1_xboole_0 @ B ) ) ) ) ) ))).
% 0.42/0.60  thf('31', plain,
% 0.42/0.60      (![X14 : $i, X15 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.42/0.60          | ~ (v1_xboole_0 @ X14)
% 0.42/0.60          | (v1_subset_1 @ X14 @ X15)
% 0.42/0.60          | (v1_xboole_0 @ X15))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc2_subset_1])).
% 0.42/0.60  thf('32', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (v1_xboole_0 @ X1)
% 0.42/0.60          | (v1_xboole_0 @ X0)
% 0.42/0.60          | (v1_subset_1 @ X1 @ X0)
% 0.42/0.60          | ~ (v1_xboole_0 @ X1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((v1_subset_1 @ X1 @ X0) | (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.60      inference('simplify', [status(thm)], ['32'])).
% 0.42/0.60  thf('34', plain, (![X13 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X13))),
% 0.42/0.60      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.42/0.60  thf('35', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (v1_xboole_0 @ X1) | (v1_subset_1 @ X1 @ (k1_tarski @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.42/0.60  thf('36', plain, (![X16 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X16) @ X16)),
% 0.42/0.60      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.42/0.60  thf('37', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (sk_B_1 @ (k1_tarski @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.42/0.60  thf('38', plain, (~ (v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['25', '37'])).
% 0.42/0.60  thf('39', plain,
% 0.42/0.60      (((v1_xboole_0 @ sk_A)
% 0.42/0.60        | ~ (v1_zfmisc_1 @ sk_A)
% 0.42/0.60        | ((sk_B_1 @ sk_A) = (sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['4', '38'])).
% 0.42/0.60  thf('40', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('41', plain, (((v1_xboole_0 @ sk_A) | ((sk_B_1 @ sk_A) = (sk_A)))),
% 0.42/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.60  thf('42', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('43', plain, (((sk_B_1 @ sk_A) = (sk_A))),
% 0.42/0.60      inference('clc', [status(thm)], ['41', '42'])).
% 0.42/0.60  thf('44', plain, (![X16 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X16) @ X16)),
% 0.42/0.60      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.42/0.60  thf('45', plain, (~ (v1_subset_1 @ sk_A @ sk_A)),
% 0.42/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.42/0.60  thf('46', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('47', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 0.42/0.60      inference('clc', [status(thm)], ['10', '11'])).
% 0.42/0.60  thf('48', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_2) @ sk_A)),
% 0.42/0.60      inference('demod', [status(thm)], ['46', '47'])).
% 0.42/0.60  thf('49', plain, (((k1_tarski @ sk_B_2) = (sk_A))),
% 0.42/0.60      inference('clc', [status(thm)], ['23', '24'])).
% 0.42/0.60  thf('50', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.42/0.60      inference('demod', [status(thm)], ['48', '49'])).
% 0.42/0.60  thf('51', plain, ($false), inference('demod', [status(thm)], ['45', '50'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
