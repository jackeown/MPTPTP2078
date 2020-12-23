%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rOrj1ZqyIx

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:08 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   54 (  65 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  394 ( 507 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( X47 != X46 )
      | ( r2_hidden @ X47 @ X48 )
      | ( X48
       != ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X46: $i] :
      ( r2_hidden @ X46 @ ( k1_tarski @ X46 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ( r2_hidden @ X12 @ X15 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      | ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X46: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X49 @ X48 )
      | ( X49 = X46 )
      | ( X48
       != ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X46: $i,X49: $i] :
      ( ( X49 = X46 )
      | ~ ( r2_hidden @ X49 @ ( k1_tarski @ X46 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r2_hidden @ X16 @ X13 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ X16 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X24: $i] :
      ( ( X22 = X24 )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k1_tarski @ X1 )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ X32 @ X33 )
      = ( k5_xboole_0 @ X32 @ ( k4_xboole_0 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X46: $i] :
      ( r2_hidden @ X46 @ ( k1_tarski @ X46 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k5_xboole_0 @ X19 @ X21 ) )
      | ( r2_hidden @ X18 @ X19 )
      | ~ ( r2_hidden @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','30'])).

thf('32',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X46: $i,X49: $i] :
      ( ( X49 = X46 )
      | ~ ( r2_hidden @ X49 @ ( k1_tarski @ X46 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('34',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rOrj1ZqyIx
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:45:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.45/1.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.45/1.66  % Solved by: fo/fo7.sh
% 1.45/1.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.45/1.66  % done 1851 iterations in 1.221s
% 1.45/1.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.45/1.66  % SZS output start Refutation
% 1.45/1.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.45/1.66  thf(sk_A_type, type, sk_A: $i).
% 1.45/1.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.45/1.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.45/1.66  thf(sk_B_type, type, sk_B: $i).
% 1.45/1.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.45/1.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.45/1.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.45/1.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.45/1.66  thf(t13_zfmisc_1, conjecture,
% 1.45/1.66    (![A:$i,B:$i]:
% 1.45/1.66     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.45/1.66         ( k1_tarski @ A ) ) =>
% 1.45/1.66       ( ( A ) = ( B ) ) ))).
% 1.45/1.66  thf(zf_stmt_0, negated_conjecture,
% 1.45/1.66    (~( ![A:$i,B:$i]:
% 1.45/1.66        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.45/1.66            ( k1_tarski @ A ) ) =>
% 1.45/1.66          ( ( A ) = ( B ) ) ) )),
% 1.45/1.66    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 1.45/1.66  thf('0', plain,
% 1.45/1.66      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.45/1.66         = (k1_tarski @ sk_A))),
% 1.45/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.66  thf(d1_tarski, axiom,
% 1.45/1.66    (![A:$i,B:$i]:
% 1.45/1.66     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.45/1.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.45/1.66  thf('1', plain,
% 1.45/1.66      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.45/1.66         (((X47) != (X46))
% 1.45/1.66          | (r2_hidden @ X47 @ X48)
% 1.45/1.66          | ((X48) != (k1_tarski @ X46)))),
% 1.45/1.66      inference('cnf', [status(esa)], [d1_tarski])).
% 1.45/1.66  thf('2', plain, (![X46 : $i]: (r2_hidden @ X46 @ (k1_tarski @ X46))),
% 1.45/1.66      inference('simplify', [status(thm)], ['1'])).
% 1.45/1.66  thf(d5_xboole_0, axiom,
% 1.45/1.66    (![A:$i,B:$i,C:$i]:
% 1.45/1.66     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.45/1.66       ( ![D:$i]:
% 1.45/1.66         ( ( r2_hidden @ D @ C ) <=>
% 1.45/1.66           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.45/1.66  thf('3', plain,
% 1.45/1.66      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.45/1.66         (~ (r2_hidden @ X12 @ X13)
% 1.45/1.66          | (r2_hidden @ X12 @ X14)
% 1.45/1.66          | (r2_hidden @ X12 @ X15)
% 1.45/1.66          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 1.45/1.66      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.45/1.66  thf('4', plain,
% 1.45/1.66      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.45/1.66         ((r2_hidden @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 1.45/1.66          | (r2_hidden @ X12 @ X14)
% 1.45/1.66          | ~ (r2_hidden @ X12 @ X13))),
% 1.45/1.66      inference('simplify', [status(thm)], ['3'])).
% 1.45/1.66  thf('5', plain,
% 1.45/1.66      (![X0 : $i, X1 : $i]:
% 1.45/1.66         ((r2_hidden @ X0 @ X1)
% 1.45/1.66          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.45/1.66      inference('sup-', [status(thm)], ['2', '4'])).
% 1.45/1.66  thf(d3_tarski, axiom,
% 1.45/1.66    (![A:$i,B:$i]:
% 1.45/1.66     ( ( r1_tarski @ A @ B ) <=>
% 1.45/1.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.45/1.66  thf('6', plain,
% 1.45/1.66      (![X3 : $i, X5 : $i]:
% 1.45/1.66         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.45/1.66      inference('cnf', [status(esa)], [d3_tarski])).
% 1.45/1.66  thf('7', plain,
% 1.45/1.66      (![X46 : $i, X48 : $i, X49 : $i]:
% 1.45/1.66         (~ (r2_hidden @ X49 @ X48)
% 1.45/1.66          | ((X49) = (X46))
% 1.45/1.66          | ((X48) != (k1_tarski @ X46)))),
% 1.45/1.66      inference('cnf', [status(esa)], [d1_tarski])).
% 1.45/1.66  thf('8', plain,
% 1.45/1.66      (![X46 : $i, X49 : $i]:
% 1.45/1.66         (((X49) = (X46)) | ~ (r2_hidden @ X49 @ (k1_tarski @ X46)))),
% 1.45/1.66      inference('simplify', [status(thm)], ['7'])).
% 1.45/1.66  thf('9', plain,
% 1.45/1.66      (![X0 : $i, X1 : $i]:
% 1.45/1.66         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.45/1.66          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.45/1.66      inference('sup-', [status(thm)], ['6', '8'])).
% 1.45/1.66  thf('10', plain,
% 1.45/1.66      (![X3 : $i, X5 : $i]:
% 1.45/1.66         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 1.45/1.66      inference('cnf', [status(esa)], [d3_tarski])).
% 1.45/1.66  thf('11', plain,
% 1.45/1.66      (![X0 : $i, X1 : $i]:
% 1.45/1.66         (~ (r2_hidden @ X0 @ X1)
% 1.45/1.66          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.45/1.66          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.45/1.66      inference('sup-', [status(thm)], ['9', '10'])).
% 1.45/1.66  thf('12', plain,
% 1.45/1.66      (![X0 : $i, X1 : $i]:
% 1.45/1.66         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.45/1.66      inference('simplify', [status(thm)], ['11'])).
% 1.45/1.66  thf('13', plain,
% 1.45/1.66      (![X0 : $i, X1 : $i]:
% 1.45/1.66         ((r2_hidden @ X1 @ X0)
% 1.45/1.66          | (r1_tarski @ (k1_tarski @ X1) @ 
% 1.45/1.66             (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 1.45/1.66      inference('sup-', [status(thm)], ['5', '12'])).
% 1.45/1.66  thf('14', plain,
% 1.45/1.66      (![X3 : $i, X5 : $i]:
% 1.45/1.66         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.45/1.66      inference('cnf', [status(esa)], [d3_tarski])).
% 1.45/1.66  thf('15', plain,
% 1.45/1.66      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.45/1.66         (~ (r2_hidden @ X16 @ X15)
% 1.45/1.66          | (r2_hidden @ X16 @ X13)
% 1.45/1.66          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 1.45/1.66      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.45/1.66  thf('16', plain,
% 1.45/1.66      (![X13 : $i, X14 : $i, X16 : $i]:
% 1.45/1.66         ((r2_hidden @ X16 @ X13)
% 1.45/1.66          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 1.45/1.66      inference('simplify', [status(thm)], ['15'])).
% 1.45/1.66  thf('17', plain,
% 1.45/1.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.66         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.45/1.66          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 1.45/1.66      inference('sup-', [status(thm)], ['14', '16'])).
% 1.45/1.66  thf('18', plain,
% 1.45/1.66      (![X3 : $i, X5 : $i]:
% 1.45/1.66         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 1.45/1.66      inference('cnf', [status(esa)], [d3_tarski])).
% 1.45/1.66  thf('19', plain,
% 1.45/1.66      (![X0 : $i, X1 : $i]:
% 1.45/1.66         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.45/1.66          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.45/1.66      inference('sup-', [status(thm)], ['17', '18'])).
% 1.45/1.66  thf('20', plain,
% 1.45/1.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 1.45/1.66      inference('simplify', [status(thm)], ['19'])).
% 1.45/1.66  thf(d10_xboole_0, axiom,
% 1.45/1.66    (![A:$i,B:$i]:
% 1.45/1.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.45/1.66  thf('21', plain,
% 1.45/1.66      (![X22 : $i, X24 : $i]:
% 1.45/1.66         (((X22) = (X24))
% 1.45/1.66          | ~ (r1_tarski @ X24 @ X22)
% 1.45/1.66          | ~ (r1_tarski @ X22 @ X24))),
% 1.45/1.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.45/1.66  thf('22', plain,
% 1.45/1.66      (![X0 : $i, X1 : $i]:
% 1.45/1.66         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.45/1.66          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.45/1.66      inference('sup-', [status(thm)], ['20', '21'])).
% 1.45/1.66  thf('23', plain,
% 1.45/1.66      (![X0 : $i, X1 : $i]:
% 1.45/1.66         ((r2_hidden @ X1 @ X0)
% 1.45/1.66          | ((k1_tarski @ X1) = (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 1.45/1.66      inference('sup-', [status(thm)], ['13', '22'])).
% 1.45/1.66  thf(t98_xboole_1, axiom,
% 1.45/1.66    (![A:$i,B:$i]:
% 1.45/1.66     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.45/1.66  thf('24', plain,
% 1.45/1.66      (![X32 : $i, X33 : $i]:
% 1.45/1.66         ((k2_xboole_0 @ X32 @ X33)
% 1.45/1.66           = (k5_xboole_0 @ X32 @ (k4_xboole_0 @ X33 @ X32)))),
% 1.45/1.66      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.45/1.66  thf('25', plain,
% 1.45/1.66      (![X0 : $i, X1 : $i]:
% 1.45/1.66         (((k2_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.45/1.66            = (k5_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.45/1.66          | (r2_hidden @ X0 @ X1))),
% 1.45/1.66      inference('sup+', [status(thm)], ['23', '24'])).
% 1.45/1.66  thf('26', plain, (![X46 : $i]: (r2_hidden @ X46 @ (k1_tarski @ X46))),
% 1.45/1.66      inference('simplify', [status(thm)], ['1'])).
% 1.45/1.66  thf(t1_xboole_0, axiom,
% 1.45/1.66    (![A:$i,B:$i,C:$i]:
% 1.45/1.66     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.45/1.66       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.45/1.66  thf('27', plain,
% 1.45/1.66      (![X18 : $i, X19 : $i, X21 : $i]:
% 1.45/1.66         ((r2_hidden @ X18 @ (k5_xboole_0 @ X19 @ X21))
% 1.45/1.66          | (r2_hidden @ X18 @ X19)
% 1.45/1.66          | ~ (r2_hidden @ X18 @ X21))),
% 1.45/1.66      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.45/1.66  thf('28', plain,
% 1.45/1.66      (![X0 : $i, X1 : $i]:
% 1.45/1.66         ((r2_hidden @ X0 @ X1)
% 1.45/1.66          | (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.45/1.66      inference('sup-', [status(thm)], ['26', '27'])).
% 1.45/1.66  thf('29', plain,
% 1.45/1.66      (![X0 : $i, X1 : $i]:
% 1.45/1.66         ((r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.45/1.66          | (r2_hidden @ X0 @ X1)
% 1.45/1.66          | (r2_hidden @ X0 @ X1))),
% 1.45/1.66      inference('sup+', [status(thm)], ['25', '28'])).
% 1.45/1.66  thf('30', plain,
% 1.45/1.66      (![X0 : $i, X1 : $i]:
% 1.45/1.66         ((r2_hidden @ X0 @ X1)
% 1.45/1.66          | (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.45/1.66      inference('simplify', [status(thm)], ['29'])).
% 1.45/1.66  thf('31', plain,
% 1.45/1.66      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 1.45/1.66        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 1.45/1.66      inference('sup+', [status(thm)], ['0', '30'])).
% 1.45/1.66  thf('32', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 1.45/1.66      inference('simplify', [status(thm)], ['31'])).
% 1.45/1.66  thf('33', plain,
% 1.45/1.66      (![X46 : $i, X49 : $i]:
% 1.45/1.66         (((X49) = (X46)) | ~ (r2_hidden @ X49 @ (k1_tarski @ X46)))),
% 1.45/1.66      inference('simplify', [status(thm)], ['7'])).
% 1.45/1.66  thf('34', plain, (((sk_B) = (sk_A))),
% 1.45/1.66      inference('sup-', [status(thm)], ['32', '33'])).
% 1.45/1.66  thf('35', plain, (((sk_A) != (sk_B))),
% 1.45/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.66  thf('36', plain, ($false),
% 1.45/1.66      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 1.45/1.66  
% 1.45/1.66  % SZS output end Refutation
% 1.45/1.66  
% 1.45/1.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
