%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hC2cvfSqIc

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  70 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  237 ( 464 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

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
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_subset_1 @ X16 @ X17 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_zfmisc_1 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
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

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X9 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X1: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference('sup-',[status(thm)],['19','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hC2cvfSqIc
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 43 iterations in 0.027s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.48  thf(t6_tex_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.48           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.48                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.48              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.48                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.21/0.48  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_k6_domain_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.48       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X12)
% 0.21/0.48          | ~ (m1_subset_1 @ X13 @ X12)
% 0.21/0.48          | (m1_subset_1 @ (k6_domain_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.48        | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.48       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X14)
% 0.21/0.48          | ~ (m1_subset_1 @ X15 @ X14)
% 0.21/0.48          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.21/0.48        | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.48        | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '7'])).
% 0.21/0.48  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('10', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf(cc2_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.21/0.48          | ~ (v1_subset_1 @ X16 @ X17)
% 0.21/0.48          | (v1_xboole_0 @ X16)
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X17)
% 0.21/0.48          | (v1_xboole_0 @ X17))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_A)
% 0.21/0.48        | ~ (v1_zfmisc_1 @ sk_A)
% 0.21/0.48        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.21/0.48        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.21/0.48  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf(t8_boole, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t8_boole])).
% 0.21/0.48  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.48  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.48  thf(t49_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i]:
% 0.21/0.48         ((k2_xboole_0 @ (k1_tarski @ X8) @ X9) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.48  thf('23', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((X0) != (k1_xboole_0))
% 0.21/0.48          | ~ (v1_xboole_0 @ X0)
% 0.21/0.48          | ~ (v1_xboole_0 @ (k1_tarski @ X1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X1 : $i]:
% 0.21/0.48         (~ (v1_xboole_0 @ (k1_tarski @ X1)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.48  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.48  thf('27', plain, (![X1 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X1))),
% 0.21/0.48      inference('simplify_reflect+', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain, ($false), inference('sup-', [status(thm)], ['19', '27'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.35/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
