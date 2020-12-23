%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KQdx05BNOO

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  72 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  247 ( 474 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ X24 )
      | ( ( k6_domain_1 @ X24 @ X25 )
        = ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( v1_subset_1 @ X26 @ X27 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v1_zfmisc_1 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('16',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['12','13','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('20',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','22'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('24',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KQdx05BNOO
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:24:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 41 iterations in 0.020s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(t6_tex_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.47           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.47                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.47              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.47                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.21/0.47  thf('0', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k6_domain_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.47       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X22 : $i, X23 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ X22)
% 0.21/0.47          | ~ (m1_subset_1 @ X23 @ X22)
% 0.21/0.47          | (m1_subset_1 @ (k6_domain_1 @ X22 @ X23) @ (k1_zfmisc_1 @ X22)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.47        | (v1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf('3', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.47       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X24 : $i, X25 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ X24)
% 0.21/0.47          | ~ (m1_subset_1 @ X25 @ X24)
% 0.21/0.47          | ((k6_domain_1 @ X24 @ X25) = (k1_tarski @ X25)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.21/0.47        | (v1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 0.21/0.47      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (((m1_subset_1 @ (k1_tarski @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.47        | (v1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '7'])).
% 0.21/0.47  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((m1_subset_1 @ (k1_tarski @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf(cc2_tex_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X26 : $i, X27 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.21/0.47          | ~ (v1_subset_1 @ X26 @ X27)
% 0.21/0.47          | (v1_xboole_0 @ X26)
% 0.21/0.47          | ~ (v1_zfmisc_1 @ X27)
% 0.21/0.47          | (v1_xboole_0 @ X27))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (((v1_xboole_0 @ sk_A)
% 0.21/0.47        | ~ (v1_zfmisc_1 @ sk_A)
% 0.21/0.47        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.21/0.47        | ~ (v1_subset_1 @ (k1_tarski @ sk_B_2) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 0.21/0.47      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_2) @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.21/0.47  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B_2))),
% 0.21/0.47      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf(t29_mcart_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.47                 ( ![C:$i,D:$i,E:$i]:
% 0.21/0.47                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.21/0.47                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X18 : $i]:
% 0.21/0.47         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X18) @ X18))),
% 0.21/0.47      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.47  thf(d1_xboole_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain, (((k1_tarski @ sk_B_2) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.47  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.47  thf('24', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.47  thf(t49_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ (k1_tarski @ X12) @ X13) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.47  thf('26', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['23', '26'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
