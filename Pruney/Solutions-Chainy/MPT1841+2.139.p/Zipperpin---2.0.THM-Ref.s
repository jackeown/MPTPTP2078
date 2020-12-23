%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WNSmvoEwqV

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  75 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  263 ( 490 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_zfmisc_1 @ X18 )
      | ( X19 = X18 )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('21',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A ) ),
    inference(clc,[status(thm)],['19','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_tarski @ sk_B_1 )
    = sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['6','26'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('28',plain,(
    ! [X10: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('29',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('30',plain,(
    ! [X10: $i] :
      ~ ( v1_subset_1 @ X10 @ X10 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference('sup-',[status(thm)],['27','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WNSmvoEwqV
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 44 iterations in 0.035s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.49  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.49  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(t6_tex_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.49           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.20/0.49                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.49              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.20/0.49                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.20/0.49  thf('0', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.49       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X16)
% 0.20/0.49          | ~ (m1_subset_1 @ X17 @ X16)
% 0.20/0.49          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.20/0.49        | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('5', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.20/0.49      inference('clc', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '5'])).
% 0.20/0.49  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_k6_domain_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.49       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X14)
% 0.20/0.49          | ~ (m1_subset_1 @ X15 @ X14)
% 0.20/0.49          | (m1_subset_1 @ (k6_domain_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.49        | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.20/0.49      inference('clc', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.49        | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('15', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf(t1_tex_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.49           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X18)
% 0.20/0.49          | ~ (v1_zfmisc_1 @ X18)
% 0.20/0.49          | ((X19) = (X18))
% 0.20/0.49          | ~ (r1_tarski @ X19 @ X18)
% 0.20/0.49          | (v1_xboole_0 @ X19))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.20/0.49        | ((k1_tarski @ sk_B_1) = (sk_A))
% 0.20/0.49        | ~ (v1_zfmisc_1 @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.20/0.49        | ((k1_tarski @ sk_B_1) = (sk_A))
% 0.20/0.49        | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf(d1_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         (((X4) != (X3)) | (r2_hidden @ X4 @ X5) | ((X5) != (k1_tarski @ X3)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.49  thf('21', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.20/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.49  thf(d1_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('23', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain, (((v1_xboole_0 @ sk_A) | ((k1_tarski @ sk_B_1) = (sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['19', '23'])).
% 0.20/0.49  thf('25', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain, (((k1_tarski @ sk_B_1) = (sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '26'])).
% 0.20/0.49  thf(fc14_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.20/0.49  thf('28', plain, (![X10 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X10) @ X10)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.20/0.49  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.49  thf('29', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.49  thf('30', plain, (![X10 : $i]: ~ (v1_subset_1 @ X10 @ X10)),
% 0.20/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain, ($false), inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
