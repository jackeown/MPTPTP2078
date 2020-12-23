%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qA1AZ8CXxs

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  53 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  266 ( 305 expanded)
%              Number of equality atoms :   29 (  33 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t27_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( ( k2_tarski @ A @ B )
        = ( k1_tarski @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( ( k2_tarski @ A @ B )
          = ( k1_tarski @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X96: $i,X97: $i] :
      ( ( X97
        = ( k1_tarski @ X96 ) )
      | ( X97 = k1_xboole_0 )
      | ~ ( r1_tarski @ X97 @ ( k1_tarski @ X96 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('2',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k2_tarski @ X55 @ X56 )
      = ( k2_xboole_0 @ ( k1_tarski @ X55 ) @ ( k1_tarski @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X53: $i,X54: $i] :
      ( r1_tarski @ X53 @ ( k2_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','9'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X44: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( r1_tarski @ X44 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('12',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X41: $i,X43: $i] :
      ( ( ( k4_xboole_0 @ X41 @ X43 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('17',plain,(
    ! [X93: $i,X94: $i] :
      ( ~ ( r2_hidden @ X93 @ X94 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X93 ) @ X94 )
       != ( k1_tarski @ X93 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(l20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf('20',plain,(
    ! [X91: $i,X92: $i] :
      ( ( r2_hidden @ X91 @ X92 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ X91 ) @ X92 ) @ X92 ) ) ),
    inference(cnf,[status(esa)],[l20_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qA1AZ8CXxs
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 115 iterations in 0.059s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(t27_zfmisc_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.20/0.50       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.50        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.20/0.50          ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t27_zfmisc_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(l3_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X96 : $i, X97 : $i]:
% 0.20/0.50         (((X97) = (k1_tarski @ X96))
% 0.20/0.50          | ((X97) = (k1_xboole_0))
% 0.20/0.50          | ~ (r1_tarski @ X97 @ (k1_tarski @ X96)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.50        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf('3', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf(t41_enumset1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k2_tarski @ A @ B ) =
% 0.20/0.50       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X55 : $i, X56 : $i]:
% 0.20/0.50         ((k2_tarski @ X55 @ X56)
% 0.20/0.50           = (k2_xboole_0 @ (k1_tarski @ X55) @ (k1_tarski @ X56)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.50  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.50  thf(t7_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X53 : $i, X54 : $i]: (r1_tarski @ X53 @ (k2_xboole_0 @ X53 @ X54))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['5', '8'])).
% 0.20/0.50  thf('10', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ k1_xboole_0)),
% 0.20/0.50      inference('sup+', [status(thm)], ['4', '9'])).
% 0.20/0.50  thf(t3_xboole_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X44 : $i]:
% 0.20/0.50         (((X44) = (k1_xboole_0)) | ~ (r1_tarski @ X44 @ k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.50  thf('12', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('14', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.20/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.50  thf(t37_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X41 : $i, X43 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ X41 @ X43) = (k1_xboole_0))
% 0.20/0.50          | ~ (r1_tarski @ X41 @ X43))),
% 0.20/0.50      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.20/0.50  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf(l33_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.50       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X93 : $i, X94 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X93 @ X94)
% 0.20/0.50          | ((k4_xboole_0 @ (k1_tarski @ X93) @ X94) != (k1_tarski @ X93)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.50  thf('19', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.50  thf(l20_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.20/0.50       ( r2_hidden @ A @ B ) ))).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X91 : $i, X92 : $i]:
% 0.20/0.50         ((r2_hidden @ X91 @ X92)
% 0.20/0.50          | ~ (r1_tarski @ (k2_xboole_0 @ (k1_tarski @ X91) @ X92) @ X92))),
% 0.20/0.50      inference('cnf', [status(esa)], [l20_zfmisc_1])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.50          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.20/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.50  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['18', '23'])).
% 0.20/0.50  thf('25', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '24'])).
% 0.20/0.50  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
