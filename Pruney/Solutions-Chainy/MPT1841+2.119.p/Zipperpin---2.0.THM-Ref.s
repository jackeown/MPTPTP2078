%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A3eBbKyJQG

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:45 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   44 (  58 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  225 ( 393 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ A )
         => ( ( A != k1_xboole_0 )
           => ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ X5 )
      | ( m1_subset_1 @ ( k2_tarski @ X6 @ X4 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ( X5 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t56_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_tarski @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k2_tarski @ sk_B @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( v1_subset_1 @ X11 @ X12 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_zfmisc_1 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( ( k6_domain_1 @ X9 @ X10 )
        = ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('14',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('21',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('22',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['20','21'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A3eBbKyJQG
% 0.14/0.38  % Computer   : n007.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 17:14:06 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.25/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.46  % Solved by: fo/fo7.sh
% 0.25/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.46  % done 27 iterations in 0.009s
% 0.25/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.46  % SZS output start Refutation
% 0.25/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.25/0.46  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.25/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.46  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.25/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.46  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.25/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.46  thf(t6_tex_2, conjecture,
% 0.25/0.46    (![A:$i]:
% 0.25/0.46     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.25/0.46       ( ![B:$i]:
% 0.25/0.46         ( ( m1_subset_1 @ B @ A ) =>
% 0.25/0.46           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.25/0.46                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.25/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.46    (~( ![A:$i]:
% 0.25/0.46        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.25/0.46          ( ![B:$i]:
% 0.25/0.46            ( ( m1_subset_1 @ B @ A ) =>
% 0.25/0.46              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.25/0.46                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.25/0.46    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.25/0.46  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf('1', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf('2', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf(t56_subset_1, axiom,
% 0.25/0.46    (![A:$i,B:$i]:
% 0.25/0.46     ( ( m1_subset_1 @ B @ A ) =>
% 0.25/0.46       ( ![C:$i]:
% 0.25/0.46         ( ( m1_subset_1 @ C @ A ) =>
% 0.25/0.46           ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.25/0.46             ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.25/0.46  thf('3', plain,
% 0.25/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.25/0.46         (~ (m1_subset_1 @ X4 @ X5)
% 0.25/0.46          | (m1_subset_1 @ (k2_tarski @ X6 @ X4) @ (k1_zfmisc_1 @ X5))
% 0.25/0.46          | ((X5) = (k1_xboole_0))
% 0.25/0.46          | ~ (m1_subset_1 @ X6 @ X5))),
% 0.25/0.46      inference('cnf', [status(esa)], [t56_subset_1])).
% 0.25/0.46  thf('4', plain,
% 0.25/0.46      (![X0 : $i]:
% 0.25/0.46         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.25/0.46          | ((sk_A) = (k1_xboole_0))
% 0.25/0.46          | (m1_subset_1 @ (k2_tarski @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.25/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.25/0.46  thf('5', plain,
% 0.25/0.46      (((m1_subset_1 @ (k2_tarski @ sk_B @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.25/0.46        | ((sk_A) = (k1_xboole_0)))),
% 0.25/0.46      inference('sup-', [status(thm)], ['1', '4'])).
% 0.25/0.46  thf(t69_enumset1, axiom,
% 0.25/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.25/0.46  thf('6', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.25/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.25/0.46  thf('7', plain,
% 0.25/0.46      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.25/0.46        | ((sk_A) = (k1_xboole_0)))),
% 0.25/0.46      inference('demod', [status(thm)], ['5', '6'])).
% 0.25/0.46  thf(cc2_tex_2, axiom,
% 0.25/0.46    (![A:$i]:
% 0.25/0.46     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.25/0.46       ( ![B:$i]:
% 0.25/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.25/0.46           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.25/0.46  thf('8', plain,
% 0.25/0.46      (![X11 : $i, X12 : $i]:
% 0.25/0.46         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.25/0.46          | ~ (v1_subset_1 @ X11 @ X12)
% 0.25/0.46          | (v1_xboole_0 @ X11)
% 0.25/0.46          | ~ (v1_zfmisc_1 @ X12)
% 0.25/0.46          | (v1_xboole_0 @ X12))),
% 0.25/0.46      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.25/0.46  thf('9', plain,
% 0.25/0.46      ((((sk_A) = (k1_xboole_0))
% 0.25/0.46        | (v1_xboole_0 @ sk_A)
% 0.25/0.46        | ~ (v1_zfmisc_1 @ sk_A)
% 0.25/0.46        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.25/0.46        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.25/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.25/0.46  thf('10', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf('11', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf('12', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf(redefinition_k6_domain_1, axiom,
% 0.25/0.46    (![A:$i,B:$i]:
% 0.25/0.46     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.25/0.46       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.25/0.46  thf('13', plain,
% 0.25/0.46      (![X9 : $i, X10 : $i]:
% 0.25/0.46         ((v1_xboole_0 @ X9)
% 0.25/0.46          | ~ (m1_subset_1 @ X10 @ X9)
% 0.25/0.46          | ((k6_domain_1 @ X9 @ X10) = (k1_tarski @ X10)))),
% 0.25/0.46      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.25/0.46  thf('14', plain,
% 0.25/0.46      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.25/0.46        | (v1_xboole_0 @ sk_A))),
% 0.25/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.25/0.46  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf('16', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.25/0.46      inference('clc', [status(thm)], ['14', '15'])).
% 0.25/0.46  thf('17', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.25/0.46      inference('demod', [status(thm)], ['11', '16'])).
% 0.25/0.46  thf('18', plain,
% 0.25/0.46      ((((sk_A) = (k1_xboole_0))
% 0.25/0.46        | (v1_xboole_0 @ sk_A)
% 0.25/0.46        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.25/0.46      inference('demod', [status(thm)], ['9', '10', '17'])).
% 0.25/0.46  thf('19', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf('20', plain,
% 0.25/0.46      (((v1_xboole_0 @ (k1_tarski @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.25/0.46      inference('clc', [status(thm)], ['18', '19'])).
% 0.25/0.46  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.25/0.46  thf('21', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X3))),
% 0.25/0.46      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.25/0.46  thf('22', plain, (((sk_A) = (k1_xboole_0))),
% 0.25/0.46      inference('clc', [status(thm)], ['20', '21'])).
% 0.25/0.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.25/0.46  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.25/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.25/0.46  thf('24', plain, ($false),
% 0.25/0.46      inference('demod', [status(thm)], ['0', '22', '23'])).
% 0.25/0.46  
% 0.25/0.46  % SZS output end Refutation
% 0.25/0.46  
% 0.25/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
