%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YBrnCIqyKY

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   59 (  80 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  299 ( 526 expanded)
%              Number of equality atoms :   25 (  28 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ X28 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ X30 )
      | ( ( k6_domain_1 @ X30 @ X31 )
        = ( k1_tarski @ X31 ) ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( v1_subset_1 @ X32 @ X33 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( v1_zfmisc_1 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
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
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ( ( k4_xboole_0 @ X22 @ ( k1_tarski @ X21 ) )
       != X22 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('29',plain,(
    ! [X7: $i,X10: $i] :
      ( r2_hidden @ X7 @ ( k2_tarski @ X10 @ X7 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['26','30'])).

thf('32',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YBrnCIqyKY
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 42 iterations in 0.023s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(t6_tex_2, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.48           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.48                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.48              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.48                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.22/0.48  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_k6_domain_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.48       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X28 : $i, X29 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X28)
% 0.22/0.48          | ~ (m1_subset_1 @ X29 @ X28)
% 0.22/0.48          | (m1_subset_1 @ (k6_domain_1 @ X28 @ X29) @ (k1_zfmisc_1 @ X28)))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.48        | (v1_xboole_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.48       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X30 : $i, X31 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X30)
% 0.22/0.48          | ~ (m1_subset_1 @ X31 @ X30)
% 0.22/0.48          | ((k6_domain_1 @ X30 @ X31) = (k1_tarski @ X31)))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.22/0.48        | (v1_xboole_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.48  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.22/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.48        | (v1_xboole_0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['2', '7'])).
% 0.22/0.48  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('10', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.48      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.48  thf(cc2_tex_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.48           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X32 : $i, X33 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 0.22/0.48          | ~ (v1_subset_1 @ X32 @ X33)
% 0.22/0.48          | (v1_xboole_0 @ X32)
% 0.22/0.48          | ~ (v1_zfmisc_1 @ X33)
% 0.22/0.48          | (v1_xboole_0 @ X33))),
% 0.22/0.48      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (((v1_xboole_0 @ sk_A)
% 0.22/0.48        | ~ (v1_zfmisc_1 @ sk_A)
% 0.22/0.48        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.22/0.48        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('14', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.22/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.22/0.48  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.22/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.22/0.48      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.22/0.48  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 0.22/0.48      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.48  thf(l13_xboole_0, axiom,
% 0.22/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.48  thf('21', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf(t1_boole, axiom,
% 0.22/0.48    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.48  thf('22', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.48  thf(t46_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.48  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.48  thf(t65_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.22/0.48       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      (![X21 : $i, X22 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X21 @ X22)
% 0.22/0.48          | ((k4_xboole_0 @ X22 @ (k1_tarski @ X21)) != (X22)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.22/0.48          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.48  thf(t69_enumset1, axiom,
% 0.22/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.48  thf('27', plain,
% 0.22/0.48      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.22/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.48  thf(d2_tarski, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.48       ( ![D:$i]:
% 0.22/0.48         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.48  thf('28', plain,
% 0.22/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.48         (((X8) != (X7))
% 0.22/0.48          | (r2_hidden @ X8 @ X9)
% 0.22/0.48          | ((X9) != (k2_tarski @ X10 @ X7)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.48  thf('29', plain,
% 0.22/0.48      (![X7 : $i, X10 : $i]: (r2_hidden @ X7 @ (k2_tarski @ X10 @ X7))),
% 0.22/0.48      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.48  thf('30', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['27', '29'])).
% 0.22/0.48  thf('31', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.22/0.48      inference('demod', [status(thm)], ['26', '30'])).
% 0.22/0.48  thf('32', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['21', '31'])).
% 0.22/0.48  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
