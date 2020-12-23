%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3rAwnNmiPj

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:43 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 117 expanded)
%              Number of leaves         :   30 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  342 ( 655 expanded)
%              Number of equality atoms :   35 (  63 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( r1_xboole_0 @ X18 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X26 ) @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X18: $i] :
      ( r1_xboole_0 @ X18 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t68_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('11',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r2_hidden @ X35 @ X36 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ X36 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t68_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X38: $i] :
      ( r1_tarski @ ( k1_tarski @ X38 ) @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('18',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ( m1_subset_1 @ X39 @ X40 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X46: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('22',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k3_subset_1 @ X48 @ ( k3_subset_1 @ X48 @ X47 ) )
        = X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k3_subset_1 @ X44 @ X45 )
        = ( k4_xboole_0 @ X44 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t22_subset_1,conjecture,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k2_subset_1 @ A )
        = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_subset_1])).

thf('29',plain,(
    ( k2_subset_1 @ sk_A )
 != ( k3_subset_1 @ sk_A @ ( k1_subset_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X42: $i] :
      ( ( k1_subset_1 @ X42 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('31',plain,(
    ( k2_subset_1 @ sk_A )
 != ( k3_subset_1 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('32',plain,(
    ! [X43: $i] :
      ( ( k2_subset_1 @ X43 )
      = X43 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('33',plain,(
    sk_A
 != ( k3_subset_1 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( sk_A
     != ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    sk_A != sk_A ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3rAwnNmiPj
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:59:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 615 iterations in 0.164s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.44/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.44/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.62  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.44/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.62  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.44/0.62  thf('0', plain, (![X18 : $i]: (r1_xboole_0 @ X18 @ k1_xboole_0)),
% 0.44/0.62      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.44/0.62  thf(t88_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r1_xboole_0 @ A @ B ) =>
% 0.44/0.62       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.44/0.62  thf('1', plain,
% 0.44/0.62      (![X25 : $i, X26 : $i]:
% 0.44/0.62         (((k4_xboole_0 @ (k2_xboole_0 @ X25 @ X26) @ X26) = (X25))
% 0.44/0.62          | ~ (r1_xboole_0 @ X25 @ X26))),
% 0.44/0.62      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.62  thf(t1_boole, axiom,
% 0.44/0.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.62  thf('3', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.44/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.44/0.62  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.44/0.62  thf(t48_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.62  thf('5', plain,
% 0.44/0.62      (![X16 : $i, X17 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.44/0.62           = (k3_xboole_0 @ X16 @ X17))),
% 0.44/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.44/0.62  thf('7', plain, (![X18 : $i]: (r1_xboole_0 @ X18 @ k1_xboole_0)),
% 0.44/0.62      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.44/0.62  thf(d7_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.44/0.62       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (![X4 : $i, X5 : $i]:
% 0.44/0.62         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.44/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.62  thf('9', plain,
% 0.44/0.62      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.62  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.62      inference('demod', [status(thm)], ['6', '9'])).
% 0.44/0.62  thf(t68_zfmisc_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.44/0.62       ( r2_hidden @ A @ B ) ))).
% 0.44/0.62  thf('11', plain,
% 0.44/0.62      (![X35 : $i, X36 : $i]:
% 0.44/0.62         ((r2_hidden @ X35 @ X36)
% 0.44/0.62          | ((k4_xboole_0 @ (k1_tarski @ X35) @ X36) != (k1_xboole_0)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t68_zfmisc_1])).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.62          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.62  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['12'])).
% 0.44/0.62  thf(t80_zfmisc_1, axiom,
% 0.44/0.62    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      (![X38 : $i]: (r1_tarski @ (k1_tarski @ X38) @ (k1_zfmisc_1 @ X38))),
% 0.44/0.62      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 0.44/0.62  thf(d3_tarski, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.62  thf('15', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X0 @ X1)
% 0.44/0.62          | (r2_hidden @ X0 @ X2)
% 0.44/0.62          | ~ (r1_tarski @ X1 @ X2))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.62          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.62  thf('17', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['13', '16'])).
% 0.44/0.62  thf(d2_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( v1_xboole_0 @ A ) =>
% 0.44/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.44/0.62       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      (![X39 : $i, X40 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X39 @ X40)
% 0.44/0.62          | (m1_subset_1 @ X39 @ X40)
% 0.44/0.62          | (v1_xboole_0 @ X40))),
% 0.44/0.62      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.44/0.62          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.62  thf(fc1_subset_1, axiom,
% 0.44/0.62    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.44/0.62  thf('20', plain, (![X46 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X46))),
% 0.44/0.62      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.44/0.62  thf('21', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.44/0.62      inference('clc', [status(thm)], ['19', '20'])).
% 0.44/0.62  thf(involutiveness_k3_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.62       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.44/0.62  thf('22', plain,
% 0.44/0.62      (![X47 : $i, X48 : $i]:
% 0.44/0.62         (((k3_subset_1 @ X48 @ (k3_subset_1 @ X48 @ X47)) = (X47))
% 0.44/0.62          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48)))),
% 0.44/0.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.44/0.62  thf('23', plain,
% 0.44/0.62      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.44/0.62  thf('24', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.44/0.62      inference('clc', [status(thm)], ['19', '20'])).
% 0.44/0.62  thf(d5_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.62       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.44/0.62  thf('25', plain,
% 0.44/0.62      (![X44 : $i, X45 : $i]:
% 0.44/0.62         (((k3_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))
% 0.44/0.62          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X44)))),
% 0.44/0.62      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.44/0.62  thf('26', plain,
% 0.44/0.62      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.44/0.62  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.62      inference('demod', [status(thm)], ['6', '9'])).
% 0.44/0.62  thf('28', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.62      inference('sup+', [status(thm)], ['26', '27'])).
% 0.44/0.62  thf(t22_subset_1, conjecture,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i]:
% 0.44/0.62        ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t22_subset_1])).
% 0.44/0.62  thf('29', plain,
% 0.44/0.62      (((k2_subset_1 @ sk_A) != (k3_subset_1 @ sk_A @ (k1_subset_1 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.44/0.62  thf('30', plain, (![X42 : $i]: ((k1_subset_1 @ X42) = (k1_xboole_0))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.44/0.62  thf('31', plain,
% 0.44/0.62      (((k2_subset_1 @ sk_A) != (k3_subset_1 @ sk_A @ k1_xboole_0))),
% 0.44/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.44/0.62  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.44/0.62  thf('32', plain, (![X43 : $i]: ((k2_subset_1 @ X43) = (X43))),
% 0.44/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.44/0.62  thf('33', plain, (((sk_A) != (k3_subset_1 @ sk_A @ k1_xboole_0))),
% 0.44/0.62      inference('demod', [status(thm)], ['31', '32'])).
% 0.44/0.62  thf('34', plain,
% 0.44/0.62      (![X0 : $i]: ((sk_A) != (k3_subset_1 @ sk_A @ (k3_subset_1 @ X0 @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['28', '33'])).
% 0.44/0.62  thf('35', plain, (((sk_A) != (sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['23', '34'])).
% 0.44/0.62  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.44/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
