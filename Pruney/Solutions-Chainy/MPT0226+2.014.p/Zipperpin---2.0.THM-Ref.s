%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SNnK3Nt8e8

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:53 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  210 ( 239 expanded)
%              Number of equality atoms :   33 (  38 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['2','7'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_tarski @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('11',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X14 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('13',plain,(
    ! [X11: $i,X14: $i] :
      ( r2_hidden @ X14 @ ( k2_tarski @ X14 @ X11 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('16',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SNnK3Nt8e8
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:25:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.45  % Solved by: fo/fo7.sh
% 0.18/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.45  % done 22 iterations in 0.013s
% 0.18/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.45  % SZS output start Refutation
% 0.18/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.45  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.18/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.18/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.18/0.45  thf(t21_zfmisc_1, conjecture,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.18/0.45         ( k1_xboole_0 ) ) =>
% 0.18/0.45       ( ( A ) = ( B ) ) ))).
% 0.18/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.45    (~( ![A:$i,B:$i]:
% 0.18/0.45        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.18/0.45            ( k1_xboole_0 ) ) =>
% 0.18/0.45          ( ( A ) = ( B ) ) ) )),
% 0.18/0.45    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.18/0.45  thf('0', plain,
% 0.18/0.45      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf(t98_xboole_1, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.18/0.45  thf('1', plain,
% 0.18/0.45      (![X2 : $i, X3 : $i]:
% 0.18/0.45         ((k2_xboole_0 @ X2 @ X3)
% 0.18/0.45           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2)))),
% 0.18/0.45      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.18/0.45  thf('2', plain,
% 0.18/0.45      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.18/0.45         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.18/0.45      inference('sup+', [status(thm)], ['0', '1'])).
% 0.18/0.45  thf(t4_boole, axiom,
% 0.18/0.45    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.18/0.45  thf('3', plain,
% 0.18/0.45      (![X1 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.18/0.45      inference('cnf', [status(esa)], [t4_boole])).
% 0.18/0.45  thf('4', plain,
% 0.18/0.45      (![X2 : $i, X3 : $i]:
% 0.18/0.45         ((k2_xboole_0 @ X2 @ X3)
% 0.18/0.45           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2)))),
% 0.18/0.45      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.18/0.45  thf('5', plain,
% 0.18/0.45      (![X0 : $i]:
% 0.18/0.45         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.18/0.45      inference('sup+', [status(thm)], ['3', '4'])).
% 0.18/0.45  thf(t1_boole, axiom,
% 0.18/0.45    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.18/0.45  thf('6', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.18/0.45      inference('cnf', [status(esa)], [t1_boole])).
% 0.18/0.45  thf('7', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.18/0.45      inference('sup+', [status(thm)], ['5', '6'])).
% 0.18/0.45  thf('8', plain,
% 0.18/0.45      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.18/0.45         = (k1_tarski @ sk_B))),
% 0.18/0.45      inference('demod', [status(thm)], ['2', '7'])).
% 0.18/0.45  thf(t41_enumset1, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( k2_tarski @ A @ B ) =
% 0.18/0.45       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.18/0.45  thf('9', plain,
% 0.18/0.45      (![X17 : $i, X18 : $i]:
% 0.18/0.45         ((k2_tarski @ X17 @ X18)
% 0.18/0.45           = (k2_xboole_0 @ (k1_tarski @ X17) @ (k1_tarski @ X18)))),
% 0.18/0.45      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.18/0.45  thf(commutativity_k2_tarski, axiom,
% 0.18/0.45    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.18/0.45  thf('10', plain,
% 0.18/0.45      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.18/0.45      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.18/0.45  thf('11', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.18/0.45      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.18/0.45  thf(d2_tarski, axiom,
% 0.18/0.45    (![A:$i,B:$i,C:$i]:
% 0.18/0.45     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.18/0.45       ( ![D:$i]:
% 0.18/0.45         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.18/0.45  thf('12', plain,
% 0.18/0.45      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.18/0.45         (((X12) != (X14))
% 0.18/0.45          | (r2_hidden @ X12 @ X13)
% 0.18/0.45          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.18/0.45      inference('cnf', [status(esa)], [d2_tarski])).
% 0.18/0.45  thf('13', plain,
% 0.18/0.45      (![X11 : $i, X14 : $i]: (r2_hidden @ X14 @ (k2_tarski @ X14 @ X11))),
% 0.18/0.45      inference('simplify', [status(thm)], ['12'])).
% 0.18/0.45  thf('14', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.18/0.45      inference('sup+', [status(thm)], ['11', '13'])).
% 0.18/0.45  thf(d1_tarski, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.18/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.18/0.45  thf('15', plain,
% 0.18/0.45      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.18/0.45         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.18/0.45      inference('cnf', [status(esa)], [d1_tarski])).
% 0.18/0.45  thf('16', plain,
% 0.18/0.45      (![X6 : $i, X9 : $i]:
% 0.18/0.45         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.18/0.45      inference('simplify', [status(thm)], ['15'])).
% 0.18/0.45  thf('17', plain, (((sk_A) = (sk_B))),
% 0.18/0.45      inference('sup-', [status(thm)], ['14', '16'])).
% 0.18/0.45  thf('18', plain, (((sk_A) != (sk_B))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('19', plain, ($false),
% 0.18/0.45      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.18/0.45  
% 0.18/0.45  % SZS output end Refutation
% 0.18/0.45  
% 0.18/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
