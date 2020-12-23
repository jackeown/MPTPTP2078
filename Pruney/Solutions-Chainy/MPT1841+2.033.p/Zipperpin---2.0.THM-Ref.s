%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SEpAI6JXdB

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  58 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  183 ( 410 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

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
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ X1 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ X3 )
      | ( ( k6_domain_1 @ X3 @ X4 )
        = ( k1_tarski @ X4 ) ) ) ),
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

thf(cc1_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ( v1_subset_1 @ B @ A )
           => ( v1_xboole_0 @ B ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_subset_1 @ X5 @ X6 )
      | ~ ( v1_zfmisc_1 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_tex_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
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

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('21',plain,(
    $false ),
    inference('sup-',[status(thm)],['19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SEpAI6JXdB
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:38:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 12 iterations in 0.010s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.47  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.47  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.47  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.47  thf(t6_tex_2, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.47           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.47                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.47          ( ![B:$i]:
% 0.22/0.47            ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.47              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.47                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.22/0.47  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(dt_k6_domain_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.47       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X1 : $i, X2 : $i]:
% 0.22/0.47         ((v1_xboole_0 @ X1)
% 0.22/0.47          | ~ (m1_subset_1 @ X2 @ X1)
% 0.22/0.47          | (m1_subset_1 @ (k6_domain_1 @ X1 @ X2) @ (k1_zfmisc_1 @ X1)))),
% 0.22/0.47      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.47        | (v1_xboole_0 @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.47  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.47       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i]:
% 0.22/0.47         ((v1_xboole_0 @ X3)
% 0.22/0.47          | ~ (m1_subset_1 @ X4 @ X3)
% 0.22/0.47          | ((k6_domain_1 @ X3 @ X4) = (k1_tarski @ X4)))),
% 0.22/0.47      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.22/0.47        | (v1_xboole_0 @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.47  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.22/0.47      inference('clc', [status(thm)], ['5', '6'])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.47        | (v1_xboole_0 @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['2', '7'])).
% 0.22/0.47  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('10', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.47      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.47  thf(cc1_tex_2, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.47           ( ( v1_subset_1 @ B @ A ) => ( v1_xboole_0 @ B ) ) ) ) ))).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (![X5 : $i, X6 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.22/0.47          | (v1_xboole_0 @ X5)
% 0.22/0.47          | ~ (v1_subset_1 @ X5 @ X6)
% 0.22/0.47          | ~ (v1_zfmisc_1 @ X6)
% 0.22/0.47          | (v1_xboole_0 @ X6))),
% 0.22/0.47      inference('cnf', [status(esa)], [cc1_tex_2])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (((v1_xboole_0 @ sk_A)
% 0.22/0.47        | ~ (v1_zfmisc_1 @ sk_A)
% 0.22/0.47        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)
% 0.22/0.47        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.47  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('14', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.22/0.47      inference('clc', [status(thm)], ['5', '6'])).
% 0.22/0.47  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.22/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.22/0.47      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.22/0.47  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 0.22/0.47      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.47  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.22/0.47  thf('20', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.22/0.47      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.22/0.47  thf('21', plain, ($false), inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
