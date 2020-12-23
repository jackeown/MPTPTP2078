%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EYGKwYF7Ou

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:22 EST 2020

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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X44 ) @ ( k1_zfmisc_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X43: $i] :
      ( ( k2_subset_1 @ X43 )
      = X43 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X44 ) ) ),
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
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
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
    ! [X45: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X45 ) ) ),
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
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('10',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('11',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X38 ) @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( r1_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( m1_subset_1 @ X40 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('19',plain,(
    ! [X40: $i,X41: $i] :
      ( ( m1_subset_1 @ X40 @ X41 )
      | ~ ( r2_hidden @ X40 @ X41 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['20','21'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
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
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EYGKwYF7Ou
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 78 iterations in 0.038s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(dt_k2_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X44 : $i]: (m1_subset_1 @ (k2_subset_1 @ X44) @ (k1_zfmisc_1 @ X44))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.49  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.49  thf('1', plain, (![X43 : $i]: ((k2_subset_1 @ X43) = (X43))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.49  thf('2', plain, (![X44 : $i]: (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X44))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(d2_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.49       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X40 : $i, X41 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X40 @ X41)
% 0.20/0.49          | (r2_hidden @ X40 @ X41)
% 0.20/0.49          | (v1_xboole_0 @ X41))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.49          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf(fc1_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.49  thf('5', plain, (![X45 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X45))),
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
% 0.20/0.49  thf('7', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X40 : $i, X41 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X40 @ X41)
% 0.20/0.49          | (r2_hidden @ X40 @ X41)
% 0.20/0.49          | (v1_xboole_0 @ X41))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.49  thf('9', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf(t37_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X35 : $i, X37 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_tarski @ X35) @ X37) | ~ (r2_hidden @ X35 @ X37))),
% 0.20/0.49      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_A) | (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf(t79_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.49       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X38 : $i, X39 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_zfmisc_1 @ X38) @ (k1_zfmisc_1 @ X39))
% 0.20/0.49          | ~ (r1_tarski @ X38 @ X39))),
% 0.20/0.49      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_A)
% 0.20/0.49        | (r1_tarski @ (k1_zfmisc_1 @ (k1_tarski @ sk_B)) @ 
% 0.20/0.49           (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf(d3_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.49          | (r2_hidden @ X0 @ X2)
% 0.20/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_A)
% 0.20/0.49          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (((r2_hidden @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.49        | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X40 : $i, X41 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X40 @ X41)
% 0.20/0.49          | (m1_subset_1 @ X40 @ X41)
% 0.20/0.49          | (v1_xboole_0 @ X41))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.49  thf(t7_boole, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]: (~ (r2_hidden @ X5 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_boole])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X40 : $i, X41 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X40 @ X41) | ~ (r2_hidden @ X40 @ X41))),
% 0.20/0.49      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_A)
% 0.20/0.49        | (m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (~ (m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf(l13_xboole_0, axiom,
% 0.20/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
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
