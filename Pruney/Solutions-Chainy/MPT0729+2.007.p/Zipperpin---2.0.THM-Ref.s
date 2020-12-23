%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fvWCBzh5KL

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 147 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  382 (1112 expanded)
%              Number of equality atoms :   35 ( 130 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( k1_ordinal1 @ X22 )
      = ( k2_xboole_0 @ X22 @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t141_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ ( k1_tarski @ X21 ) ) @ ( k1_tarski @ X21 ) )
        = X20 )
      | ( r2_hidden @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t141_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r2_hidden @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t12_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k1_ordinal1 @ A )
        = ( k1_ordinal1 @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k1_ordinal1 @ A )
          = ( k1_ordinal1 @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_ordinal1])).

thf('3',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('4',plain,(
    ! [X23: $i] :
      ( r2_hidden @ X23 @ ( k1_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('5',plain,(
    r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ( X15 = X14 )
      | ( X15 = X11 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('12',plain,(
    ! [X11: $i,X14: $i,X15: $i] :
      ( ( X15 = X11 )
      | ( X15 = X14 )
      | ~ ( r2_hidden @ X15 @ ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r2_hidden @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = sk_B )
    | ( r2_hidden @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X23: $i] :
      ( r2_hidden @ X23 @ ( k1_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_hidden @ sk_B @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_tarski @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['32','34'])).

thf('36',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['19','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('38',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['19','35'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fvWCBzh5KL
% 0.11/0.33  % Computer   : n014.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:24:37 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.11/0.34  % Running portfolio for 600 s
% 0.11/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.34  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 83 iterations in 0.042s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.19/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.49  thf(d1_ordinal1, axiom,
% 0.19/0.49    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (![X22 : $i]:
% 0.19/0.49         ((k1_ordinal1 @ X22) = (k2_xboole_0 @ X22 @ (k1_tarski @ X22)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.19/0.49  thf(t141_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ~( r2_hidden @ A @ B ) ) =>
% 0.19/0.49       ( ( k4_xboole_0 @
% 0.19/0.49           ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.19/0.49         ( B ) ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X20 : $i, X21 : $i]:
% 0.19/0.49         (((k4_xboole_0 @ (k2_xboole_0 @ X20 @ (k1_tarski @ X21)) @ 
% 0.19/0.49            (k1_tarski @ X21)) = (X20))
% 0.19/0.49          | (r2_hidden @ X21 @ X20))),
% 0.19/0.49      inference('cnf', [status(esa)], [t141_zfmisc_1])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k4_xboole_0 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0)) = (X0))
% 0.19/0.49          | (r2_hidden @ X0 @ X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['0', '1'])).
% 0.19/0.49  thf(t12_ordinal1, conjecture,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i]:
% 0.19/0.49        ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t12_ordinal1])).
% 0.19/0.49  thf('3', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.19/0.49  thf('4', plain, (![X23 : $i]: (r2_hidden @ X23 @ (k1_ordinal1 @ X23))),
% 0.19/0.49      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.19/0.49  thf('5', plain, ((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.49  thf(d5_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.49       ( ![D:$i]:
% 0.19/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.49           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X2 @ X3)
% 0.19/0.49          | (r2_hidden @ X2 @ X4)
% 0.19/0.49          | (r2_hidden @ X2 @ X5)
% 0.19/0.49          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.49         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.19/0.49          | (r2_hidden @ X2 @ X4)
% 0.19/0.49          | ~ (r2_hidden @ X2 @ X3))),
% 0.19/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r2_hidden @ sk_B @ X0)
% 0.19/0.49          | (r2_hidden @ sk_B @ (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['5', '7'])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (((r2_hidden @ sk_B @ sk_A)
% 0.19/0.49        | (r2_hidden @ sk_A @ sk_A)
% 0.19/0.49        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['2', '8'])).
% 0.19/0.49  thf(t69_enumset1, axiom,
% 0.19/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.19/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.49  thf(d2_tarski, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.19/0.49       ( ![D:$i]:
% 0.19/0.49         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X11 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X15 @ X13)
% 0.19/0.49          | ((X15) = (X14))
% 0.19/0.49          | ((X15) = (X11))
% 0.19/0.49          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d2_tarski])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X11 : $i, X14 : $i, X15 : $i]:
% 0.19/0.49         (((X15) = (X11))
% 0.19/0.49          | ((X15) = (X14))
% 0.19/0.49          | ~ (r2_hidden @ X15 @ (k2_tarski @ X14 @ X11)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['10', '12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (((r2_hidden @ sk_A @ sk_A)
% 0.19/0.49        | (r2_hidden @ sk_B @ sk_A)
% 0.19/0.49        | ((sk_B) = (sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['9', '14'])).
% 0.19/0.49  thf('16', plain, (((sk_A) != (sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('17', plain, (((r2_hidden @ sk_A @ sk_A) | (r2_hidden @ sk_B @ sk_A))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf(antisymmetry_r2_hidden, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.19/0.49      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.19/0.49  thf('19', plain, (((r2_hidden @ sk_A @ sk_A) | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.49  thf('20', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k4_xboole_0 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0)) = (X0))
% 0.19/0.49          | (r2_hidden @ X0 @ X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['0', '1'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      ((((k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ sk_B)) = (sk_B))
% 0.19/0.49        | (r2_hidden @ sk_B @ sk_B))),
% 0.19/0.49      inference('sup+', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('23', plain, (![X23 : $i]: (r2_hidden @ X23 @ (k1_ordinal1 @ X23))),
% 0.19/0.49      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.49         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.19/0.49          | (r2_hidden @ X2 @ X4)
% 0.19/0.49          | ~ (r2_hidden @ X2 @ X3))),
% 0.19/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r2_hidden @ X0 @ X1)
% 0.19/0.49          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_ordinal1 @ X0) @ X1)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (((r2_hidden @ sk_A @ sk_B)
% 0.19/0.49        | (r2_hidden @ sk_B @ sk_B)
% 0.19/0.49        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['22', '25'])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (((r2_hidden @ sk_B @ sk_B)
% 0.19/0.49        | (r2_hidden @ sk_A @ sk_B)
% 0.19/0.49        | ((sk_A) = (sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.49  thf('29', plain, (((sk_A) != (sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('30', plain, (((r2_hidden @ sk_B @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf(t7_ordinal1, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (![X24 : $i, X25 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.49  thf('32', plain, (((r2_hidden @ sk_A @ sk_B) | ~ (r1_tarski @ sk_B @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.49  thf(d10_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.49  thf('34', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.19/0.49      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.49  thf('35', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.19/0.49      inference('demod', [status(thm)], ['32', '34'])).
% 0.19/0.49  thf('36', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.19/0.49      inference('demod', [status(thm)], ['19', '35'])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.19/0.49      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.19/0.49  thf('38', plain, (~ (r2_hidden @ sk_A @ sk_A)),
% 0.19/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.49  thf('39', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.19/0.49      inference('demod', [status(thm)], ['19', '35'])).
% 0.19/0.49  thf('40', plain, ($false), inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
