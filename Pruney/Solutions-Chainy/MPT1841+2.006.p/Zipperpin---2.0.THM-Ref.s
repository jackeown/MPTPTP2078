%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YCjTkrHzEs

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 (  86 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  364 ( 591 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ X24 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ X24 ) ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( ( k6_domain_1 @ X26 @ X27 )
        = ( k1_tarski @ X27 ) ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( v1_subset_1 @ X28 @ X29 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( v1_zfmisc_1 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X7 @ X11 )
      | ( X11
       != ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k1_enumset1 @ X10 @ X9 @ X8 ) )
      | ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3 != X2 )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ~ ( zip_tseitin_0 @ X2 @ X4 @ X5 @ X2 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    $false ),
    inference('sup-',[status(thm)],['32','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YCjTkrHzEs
% 0.16/0.36  % Computer   : n019.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 17:52:22 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 44 iterations in 0.022s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(t6_tex_2, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.50           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.50                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.50              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.50                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.22/0.50  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(dt_k6_domain_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.50       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X24 : $i, X25 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X24)
% 0.22/0.50          | ~ (m1_subset_1 @ X25 @ X24)
% 0.22/0.50          | (m1_subset_1 @ (k6_domain_1 @ X24 @ X25) @ (k1_zfmisc_1 @ X24)))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.50        | (v1_xboole_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.50       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X26 : $i, X27 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X26)
% 0.22/0.50          | ~ (m1_subset_1 @ X27 @ X26)
% 0.22/0.50          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.22/0.50        | (v1_xboole_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.22/0.50      inference('clc', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.50        | (v1_xboole_0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '7'])).
% 0.22/0.50  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('10', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf(cc2_tex_2, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X28 : $i, X29 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.22/0.50          | ~ (v1_subset_1 @ X28 @ X29)
% 0.22/0.50          | (v1_xboole_0 @ X28)
% 0.22/0.50          | ~ (v1_zfmisc_1 @ X29)
% 0.22/0.50          | (v1_xboole_0 @ X29))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_A)
% 0.22/0.50        | ~ (v1_zfmisc_1 @ sk_A)
% 0.22/0.50        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.22/0.50        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('14', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.22/0.50      inference('clc', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.22/0.50      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.22/0.50  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 0.22/0.50      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf(l13_xboole_0, axiom,
% 0.22/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.50  thf('21', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf(t69_enumset1, axiom,
% 0.22/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.50  thf(t70_enumset1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X15 : $i, X16 : $i]:
% 0.22/0.50         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.50  thf(d1_enumset1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.50       ( ![E:$i]:
% 0.22/0.50         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_2, axiom,
% 0.22/0.50    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_3, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.50       ( ![E:$i]:
% 0.22/0.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.50         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.22/0.50          | (r2_hidden @ X7 @ X11)
% 0.22/0.50          | ((X11) != (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.50         ((r2_hidden @ X7 @ (k1_enumset1 @ X10 @ X9 @ X8))
% 0.22/0.50          | (zip_tseitin_0 @ X7 @ X8 @ X9 @ X10))),
% 0.22/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.50  thf(t7_ordinal1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X22 : $i, X23 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.22/0.50          | ~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3))),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.22/0.50          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['23', '27'])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.22/0.50          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['22', '28'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.22/0.50          | (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['21', '29'])).
% 0.22/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.50  thf('31', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf('32', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B)),
% 0.22/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.50         (((X3) != (X2)) | ~ (zip_tseitin_0 @ X3 @ X4 @ X5 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X2 : $i, X4 : $i, X5 : $i]: ~ (zip_tseitin_0 @ X2 @ X4 @ X5 @ X2)),
% 0.22/0.50      inference('simplify', [status(thm)], ['33'])).
% 0.22/0.50  thf('35', plain, ($false), inference('sup-', [status(thm)], ['32', '34'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
