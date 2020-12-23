%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NP3lR3yCRm

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 (  79 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  270 ( 497 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( ( k6_domain_1 @ X21 @ X22 )
        = ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( v1_subset_1 @ X23 @ X24 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( v1_zfmisc_1 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('16',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('22',plain,(
    ! [X15: $i] :
      ( ( k1_ordinal1 @ X15 )
      = ( k2_xboole_0 @ X15 @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('23',plain,
    ( ( k1_ordinal1 @ sk_B )
    = ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('25',plain,
    ( ( k1_ordinal1 @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('26',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['29','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NP3lR3yCRm
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:12:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 28 iterations in 0.010s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.43  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.43  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.43  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.43  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.43  thf(t6_tex_2, conjecture,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.43       ( ![B:$i]:
% 0.20/0.43         ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.43           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.20/0.43                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i]:
% 0.20/0.43        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.43          ( ![B:$i]:
% 0.20/0.43            ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.43              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.20/0.43                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.20/0.43  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(dt_k6_domain_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.43       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.43  thf('1', plain,
% 0.20/0.43      (![X19 : $i, X20 : $i]:
% 0.20/0.43         ((v1_xboole_0 @ X19)
% 0.20/0.43          | ~ (m1_subset_1 @ X20 @ X19)
% 0.20/0.43          | (m1_subset_1 @ (k6_domain_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19)))),
% 0.20/0.43      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.43  thf('2', plain,
% 0.20/0.43      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.43        | (v1_xboole_0 @ sk_A))),
% 0.20/0.43      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.43  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.43       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.43  thf('4', plain,
% 0.20/0.43      (![X21 : $i, X22 : $i]:
% 0.20/0.43         ((v1_xboole_0 @ X21)
% 0.20/0.43          | ~ (m1_subset_1 @ X22 @ X21)
% 0.20/0.43          | ((k6_domain_1 @ X21 @ X22) = (k1_tarski @ X22)))),
% 0.20/0.43      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.20/0.43        | (v1_xboole_0 @ sk_A))),
% 0.20/0.43      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.43  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.20/0.43      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.43  thf('8', plain,
% 0.20/0.43      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.43        | (v1_xboole_0 @ sk_A))),
% 0.20/0.43      inference('demod', [status(thm)], ['2', '7'])).
% 0.20/0.43  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('10', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.43      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.43  thf(cc2_tex_2, axiom,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.20/0.43       ( ![B:$i]:
% 0.20/0.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.43           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.20/0.43  thf('11', plain,
% 0.20/0.43      (![X23 : $i, X24 : $i]:
% 0.20/0.43         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.20/0.43          | ~ (v1_subset_1 @ X23 @ X24)
% 0.20/0.43          | (v1_xboole_0 @ X23)
% 0.20/0.43          | ~ (v1_zfmisc_1 @ X24)
% 0.20/0.43          | (v1_xboole_0 @ X24))),
% 0.20/0.43      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.20/0.43  thf('12', plain,
% 0.20/0.43      (((v1_xboole_0 @ sk_A)
% 0.20/0.43        | ~ (v1_zfmisc_1 @ sk_A)
% 0.20/0.43        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.20/0.43        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.43      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.43  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('14', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.20/0.43      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.43  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.20/0.43      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.43  thf('17', plain,
% 0.20/0.43      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.20/0.43      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.20/0.43  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 0.20/0.43      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.43  thf(l13_xboole_0, axiom,
% 0.20/0.43    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.43  thf('20', plain,
% 0.20/0.43      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.43      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.43  thf('21', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.43  thf(d1_ordinal1, axiom,
% 0.20/0.43    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.20/0.43  thf('22', plain,
% 0.20/0.43      (![X15 : $i]:
% 0.20/0.43         ((k1_ordinal1 @ X15) = (k2_xboole_0 @ X15 @ (k1_tarski @ X15)))),
% 0.20/0.43      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.20/0.43  thf('23', plain,
% 0.20/0.43      (((k1_ordinal1 @ sk_B) = (k2_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.20/0.43      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.43  thf(t1_boole, axiom,
% 0.20/0.43    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.43  thf('24', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.43      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.43  thf('25', plain, (((k1_ordinal1 @ sk_B) = (sk_B))),
% 0.20/0.43      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.43  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.20/0.43  thf('26', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_ordinal1 @ X16))),
% 0.20/0.43      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.20/0.43  thf(t7_ordinal1, axiom,
% 0.20/0.43    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.43  thf('27', plain,
% 0.20/0.43      (![X17 : $i, X18 : $i]:
% 0.20/0.43         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.20/0.43      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.43  thf('28', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.20/0.43      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.43  thf('29', plain, (~ (r1_tarski @ sk_B @ sk_B)),
% 0.20/0.43      inference('sup-', [status(thm)], ['25', '28'])).
% 0.20/0.43  thf(d10_xboole_0, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.43  thf('30', plain,
% 0.20/0.43      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.20/0.43      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.43  thf('31', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.20/0.43      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.43  thf('32', plain, ($false), inference('demod', [status(thm)], ['29', '31'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
