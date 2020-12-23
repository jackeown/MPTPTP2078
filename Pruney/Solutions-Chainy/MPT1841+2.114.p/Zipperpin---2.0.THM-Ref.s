%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R6Ed4BWau1

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 122 expanded)
%              Number of leaves         :   28 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  366 ( 845 expanded)
%              Number of equality atoms :   38 (  47 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ X44 )
      | ( ( k6_domain_1 @ X44 @ X45 )
        = ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('2',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ X42 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X42 @ X43 ) @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( v1_subset_1 @ X46 @ X47 )
      | ( v1_xboole_0 @ X46 )
      | ~ ( v1_zfmisc_1 @ X47 )
      | ( v1_xboole_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('11',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k6_domain_1 @ sk_A @ sk_B ) )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k6_domain_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_xboole_0 @ ( k6_domain_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','18'])).

thf('20',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','18'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('21',plain,(
    ! [X39: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('22',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_B ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_tarski @ ( k1_setfam_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['19','22'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('24',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33 != X32 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X32 ) )
       != ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('25',plain,(
    ! [X32: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X32 ) )
     != ( k1_tarski @ X32 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X32: $i] :
      ( ( k6_subset_1 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X32 ) )
     != ( k1_tarski @ X32 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X39: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X32: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X32 ) ) ),
    inference(demod,[status(thm)],['27','38'])).

thf('40',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R6Ed4BWau1
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:35:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 50 iterations in 0.023s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.48  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
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
% 0.21/0.48  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.48       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X44 : $i, X45 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X44)
% 0.21/0.48          | ~ (m1_subset_1 @ X45 @ X44)
% 0.21/0.48          | ((k6_domain_1 @ X44 @ X45) = (k1_tarski @ X45)))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.21/0.48        | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_k6_domain_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.48       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X42 : $i, X43 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X42)
% 0.21/0.48          | ~ (m1_subset_1 @ X43 @ X42)
% 0.21/0.48          | (m1_subset_1 @ (k6_domain_1 @ X42 @ X43) @ (k1_zfmisc_1 @ X42)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.48        | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      ((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf(cc2_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X46 : $i, X47 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 0.21/0.48          | ~ (v1_subset_1 @ X46 @ X47)
% 0.21/0.48          | (v1_xboole_0 @ X46)
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X47)
% 0.21/0.48          | (v1_xboole_0 @ X47))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_A)
% 0.21/0.48        | ~ (v1_zfmisc_1 @ sk_A)
% 0.21/0.48        | (v1_xboole_0 @ (k6_domain_1 @ sk_A @ sk_B))
% 0.21/0.48        | ~ (v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('13', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k6_domain_1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.48  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain, ((v1_xboole_0 @ (k6_domain_1 @ sk_A @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf(l13_xboole_0, axiom,
% 0.21/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.48  thf('18', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['4', '18'])).
% 0.21/0.48  thf('20', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['4', '18'])).
% 0.21/0.48  thf(t11_setfam_1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.21/0.48  thf('21', plain, (![X39 : $i]: ((k1_setfam_1 @ (k1_tarski @ X39)) = (X39))),
% 0.21/0.48      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.21/0.48  thf('22', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_B))),
% 0.21/0.48      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (((k1_tarski @ (k1_setfam_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '22'])).
% 0.21/0.48  thf(t20_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.48         ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ( A ) != ( B ) ) ))).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X32 : $i, X33 : $i]:
% 0.21/0.48         (((X33) != (X32))
% 0.21/0.48          | ((k4_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X32))
% 0.21/0.48              != (k1_tarski @ X33)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X32 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X32))
% 0.21/0.48           != (k1_tarski @ X32))),
% 0.21/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.48  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X35 : $i, X36 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X32 : $i]:
% 0.21/0.48         ((k6_subset_1 @ (k1_tarski @ X32) @ (k1_tarski @ X32))
% 0.21/0.48           != (k1_tarski @ X32))),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf(t69_enumset1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.48  thf('28', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf('29', plain, (![X39 : $i]: ((k1_setfam_1 @ (k1_tarski @ X39)) = (X39))),
% 0.21/0.48      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.48  thf(t12_setfam_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X40 : $i, X41 : $i]:
% 0.21/0.48         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 0.21/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.48  thf('32', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.48  thf(t100_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ X1 @ X2)
% 0.21/0.48           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (![X35 : $i, X36 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X1 @ X2)
% 0.21/0.48           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['32', '35'])).
% 0.21/0.48  thf(t92_xboole_1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.48  thf('37', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.48  thf('38', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('39', plain, (![X32 : $i]: ((k1_xboole_0) != (k1_tarski @ X32))),
% 0.21/0.48      inference('demod', [status(thm)], ['27', '38'])).
% 0.21/0.48  thf('40', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['23', '39'])).
% 0.21/0.48  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.35/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
