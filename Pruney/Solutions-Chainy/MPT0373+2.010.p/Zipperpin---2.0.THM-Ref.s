%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.22XmgqCTif

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  54 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  235 ( 309 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X45 ) @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X44: $i] :
      ( ( k2_subset_1 @ X44 )
      = X44 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ X42 )
      | ( r2_hidden @ X41 @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X46: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(t55_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ A )
       => ( ( A != k1_xboole_0 )
         => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_subset_1])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ X42 )
      | ( r2_hidden @ X41 @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('10',plain,(
    ! [X36: $i,X38: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X36 ) @ X38 )
      | ~ ( r2_hidden @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('11',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X39 ) @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( r1_tarski @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ( m1_subset_1 @ X41 @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X41: $i,X42: $i] :
      ( ( m1_subset_1 @ X41 @ X42 )
      | ~ ( r2_hidden @ X41 @ X42 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['20','21'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.22XmgqCTif
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 78 iterations in 0.036s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(dt_k2_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X45 : $i]: (m1_subset_1 @ (k2_subset_1 @ X45) @ (k1_zfmisc_1 @ X45))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.49  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.49  thf('1', plain, (![X44 : $i]: ((k2_subset_1 @ X44) = (X44))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.49  thf('2', plain, (![X45 : $i]: (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X45))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(d2_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.49       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X41 : $i, X42 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X41 @ X42)
% 0.20/0.49          | (r2_hidden @ X41 @ X42)
% 0.20/0.49          | (v1_xboole_0 @ X42))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.49          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf(fc1_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.49  thf('5', plain, (![X46 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X46))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.49  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf(t55_subset_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.49       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.49         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.49          ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.49            ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t55_subset_1])).
% 0.20/0.49  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X41 : $i, X42 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X41 @ X42)
% 0.20/0.49          | (r2_hidden @ X41 @ X42)
% 0.20/0.49          | (v1_xboole_0 @ X42))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.49  thf('9', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf(t37_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X36 : $i, X38 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_tarski @ X36) @ X38) | ~ (r2_hidden @ X36 @ X38))),
% 0.20/0.49      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_A) | (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf(t79_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.49       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X39 : $i, X40 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_zfmisc_1 @ X39) @ (k1_zfmisc_1 @ X40))
% 0.20/0.49          | ~ (r1_tarski @ X39 @ X40))),
% 0.20/0.49      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_A)
% 0.20/0.49        | (r1_tarski @ (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)) @ 
% 0.20/0.49           (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf(d3_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.49          | (r2_hidden @ X3 @ X5)
% 0.20/0.49          | ~ (r1_tarski @ X4 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_A)
% 0.20/0.49          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k1_tarski @ sk_B_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (((r2_hidden @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.49        | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X41 : $i, X42 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X41 @ X42)
% 0.20/0.49          | (m1_subset_1 @ X41 @ X42)
% 0.20/0.49          | (v1_xboole_0 @ X42))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.49  thf(d1_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X41 : $i, X42 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X41 @ X42) | ~ (r2_hidden @ X41 @ X42))),
% 0.20/0.49      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_A)
% 0.20/0.49        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (~ (m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf(l13_xboole_0, axiom,
% 0.20/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.49  thf('24', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
