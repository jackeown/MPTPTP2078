%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7SibroOd5A

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:46 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   54 (  68 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  363 ( 494 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t82_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) )
        = ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) )
     => ( r3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) )
          = ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) )
       => ( r3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t82_zfmisc_1])).

thf('0',plain,(
    ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ X39 @ X40 )
      | ( r2_hidden @ X39 @ X41 )
      | ( X41
       != ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r2_hidden @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( r1_tarski @ X39 @ X40 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
    = ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X42 @ X41 )
      | ( r1_tarski @ X42 @ X40 )
      | ( X41
       != ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r1_tarski @ X42 @ X40 )
      | ~ ( r2_hidden @ X42 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r1_tarski @ X42 @ X40 )
      | ~ ( r2_hidden @ X42 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('15',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X37: $i,X38: $i] :
      ( r1_tarski @ X37 @ ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X37: $i,X38: $i] :
      ( r1_tarski @ X37 @ ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_B )
    | ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X37: $i,X38: $i] :
      ( r1_tarski @ X37 @ ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        | ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r3_xboole_0 @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r3_xboole_0 @ sk_A @ sk_B )
    | ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X37: $i,X38: $i] :
      ( r1_tarski @ X37 @ ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r3_xboole_0 @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    r3_xboole_0 @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7SibroOd5A
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 476 iterations in 0.190s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(r3_xboole_0_type, type, r3_xboole_0: $i > $i > $o).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(t82_zfmisc_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) =
% 0.46/0.64         ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) =>
% 0.46/0.64       ( r3_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i]:
% 0.46/0.64        ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) =
% 0.46/0.64            ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) =>
% 0.46/0.64          ( r3_xboole_0 @ A @ B ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t82_zfmisc_1])).
% 0.46/0.64  thf('0', plain, (~ (r3_xboole_0 @ sk_A @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(d10_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('2', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.46/0.64      inference('simplify', [status(thm)], ['1'])).
% 0.46/0.64  thf(d1_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.46/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X39 @ X40)
% 0.46/0.64          | (r2_hidden @ X39 @ X41)
% 0.46/0.64          | ((X41) != (k1_zfmisc_1 @ X40)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X39 : $i, X40 : $i]:
% 0.46/0.64         ((r2_hidden @ X39 @ (k1_zfmisc_1 @ X40)) | ~ (r1_tarski @ X39 @ X40))),
% 0.46/0.64      inference('simplify', [status(thm)], ['3'])).
% 0.46/0.64  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['2', '4'])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (((k2_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.46/0.64         = (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(d3_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.46/0.64       ( ![D:$i]:
% 0.46/0.64         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.64           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X6 @ X4)
% 0.46/0.64          | (r2_hidden @ X6 @ X5)
% 0.46/0.64          | (r2_hidden @ X6 @ X3)
% 0.46/0.64          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.46/0.64         ((r2_hidden @ X6 @ X3)
% 0.46/0.64          | (r2_hidden @ X6 @ X5)
% 0.46/0.64          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['7'])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))
% 0.46/0.64          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.64          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['6', '8'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (((r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))
% 0.46/0.64        | (r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '9'])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X42 @ X41)
% 0.46/0.64          | (r1_tarski @ X42 @ X40)
% 0.46/0.64          | ((X41) != (k1_zfmisc_1 @ X40)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X40 : $i, X42 : $i]:
% 0.46/0.64         ((r1_tarski @ X42 @ X40) | ~ (r2_hidden @ X42 @ (k1_zfmisc_1 @ X40)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (((r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.64        | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['10', '12'])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X40 : $i, X42 : $i]:
% 0.46/0.64         ((r1_tarski @ X42 @ X40) | ~ (r2_hidden @ X42 @ (k1_zfmisc_1 @ X40)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.46/0.64        | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.64  thf(commutativity_k2_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.64  thf(t7_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X37 : $i, X38 : $i]: (r1_tarski @ X37 @ (k2_xboole_0 @ X37 @ X38))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X10 : $i, X12 : $i]:
% 0.46/0.64         (((X10) = (X12))
% 0.46/0.64          | ~ (r1_tarski @ X12 @ X10)
% 0.46/0.64          | ~ (r1_tarski @ X10 @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.64          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 0.46/0.64        | ((k2_xboole_0 @ sk_A @ sk_B) = (sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '20'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X37 : $i, X38 : $i]: (r1_tarski @ X37 @ (k2_xboole_0 @ X37 @ X38))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X10 : $i, X12 : $i]:
% 0.46/0.64         (((X10) = (X12))
% 0.46/0.64          | ~ (r1_tarski @ X12 @ X10)
% 0.46/0.64          | ~ (r1_tarski @ X10 @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.64          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      ((((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))
% 0.46/0.64        | ((k2_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['21', '24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X37 : $i, X38 : $i]: (r1_tarski @ X37 @ (k2_xboole_0 @ X37 @ X38))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.64  thf(d9_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r3_xboole_0 @ A @ B ) <=>
% 0.46/0.64       ( ( r1_tarski @ A @ B ) | ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i]:
% 0.46/0.64         ((r3_xboole_0 @ X14 @ X15) | ~ (r1_tarski @ X14 @ X15))),
% 0.46/0.64      inference('cnf', [status(esa)], [d9_xboole_0])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (r3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (((r3_xboole_0 @ sk_A @ sk_B) | ((k2_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['25', '28'])).
% 0.46/0.64  thf('30', plain, (~ (r3_xboole_0 @ sk_A @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('31', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.46/0.64      inference('clc', [status(thm)], ['29', '30'])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X37 : $i, X38 : $i]: (r1_tarski @ X37 @ (k2_xboole_0 @ X37 @ X38))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i]:
% 0.46/0.64         ((r3_xboole_0 @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [d9_xboole_0])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (r3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)),
% 0.46/0.64      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (r3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)),
% 0.46/0.64      inference('sup+', [status(thm)], ['32', '35'])).
% 0.46/0.64  thf('37', plain, ((r3_xboole_0 @ sk_A @ sk_B)),
% 0.46/0.64      inference('sup+', [status(thm)], ['31', '36'])).
% 0.46/0.64  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
