%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3UG0czzBEU

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  52 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  205 ( 349 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( v1_subset_1 @ X14 @ X15 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_zfmisc_1 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_xboole_0 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( ( k6_domain_1 @ X12 @ X13 )
        = ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('14',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference('sup-',[status(thm)],['17','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3UG0czzBEU
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 19 iterations in 0.015s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.47  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
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
% 0.21/0.47  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k6_domain_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.47       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ X10)
% 0.21/0.47          | ~ (m1_subset_1 @ X11 @ X10)
% 0.21/0.47          | (m1_subset_1 @ (k6_domain_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.47        | (v1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf('3', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(cc2_tex_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X14 : $i, X15 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.21/0.47          | ~ (v1_subset_1 @ X14 @ X15)
% 0.21/0.47          | (v1_xboole_0 @ X14)
% 0.21/0.47          | ~ (v1_zfmisc_1 @ X15)
% 0.21/0.47          | (v1_xboole_0 @ X15))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (((v1_xboole_0 @ sk_A)
% 0.21/0.47        | ~ (v1_zfmisc_1 @ sk_A)
% 0.21/0.47        | (v1_xboole_0 @ (k6_domain_1 @ sk_A @ sk_B_1))
% 0.21/0.47        | ~ (v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('8', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k6_domain_1 @ sk_A @ sk_B_1)))),
% 0.21/0.47      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.47  thf('10', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('11', plain, ((v1_xboole_0 @ (k6_domain_1 @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('clc', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.47       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ X12)
% 0.21/0.47          | ~ (m1_subset_1 @ X13 @ X12)
% 0.21/0.47          | ((k6_domain_1 @ X12 @ X13) = (k1_tarski @ X13)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.21/0.47        | (v1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.21/0.47      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B_1))),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.47  thf(d1_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.47         (((X4) != (X3)) | (r2_hidden @ X4 @ X5) | ((X5) != (k1_tarski @ X3)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.47  thf('19', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.21/0.47      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.47  thf(d1_xboole_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.47  thf('21', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain, ($false), inference('sup-', [status(thm)], ['17', '21'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
