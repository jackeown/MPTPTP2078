%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RvDY0PlRmX

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:40 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  166 ( 173 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('10',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
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

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('13',plain,(
    ! [X11: $i,X14: $i] :
      ( r2_hidden @ X11 @ ( k2_tarski @ X14 @ X11 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RvDY0PlRmX
% 0.14/0.37  % Computer   : n011.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 16:34:27 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 33 iterations in 0.018s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.24/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.50  thf(t49_zfmisc_1, conjecture,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i,B:$i]:
% 0.24/0.50        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(commutativity_k2_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.24/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.24/0.50  thf(t7_xboole_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.24/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.24/0.50      inference('sup+', [status(thm)], ['3', '4'])).
% 0.24/0.50  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.24/0.50      inference('sup+', [status(thm)], ['2', '5'])).
% 0.24/0.50  thf(d10_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.50  thf('7', plain,
% 0.24/0.50      (![X5 : $i, X7 : $i]:
% 0.24/0.50         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.24/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.50  thf('8', plain,
% 0.24/0.50      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_A))
% 0.24/0.50        | ((k1_xboole_0) = (k1_tarski @ sk_A)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.24/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.24/0.50  thf('9', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.24/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.24/0.50  thf('10', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.24/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.24/0.50  thf(t69_enumset1, axiom,
% 0.24/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.24/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.50  thf(d2_tarski, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.24/0.50       ( ![D:$i]:
% 0.24/0.50         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.24/0.50  thf('12', plain,
% 0.24/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.24/0.50         (((X12) != (X11))
% 0.24/0.50          | (r2_hidden @ X12 @ X13)
% 0.24/0.50          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.24/0.50      inference('cnf', [status(esa)], [d2_tarski])).
% 0.24/0.50  thf('13', plain,
% 0.24/0.50      (![X11 : $i, X14 : $i]: (r2_hidden @ X11 @ (k2_tarski @ X14 @ X11))),
% 0.24/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.24/0.50  thf(d1_xboole_0, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.24/0.50  thf('14', plain,
% 0.24/0.50      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.24/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.24/0.50  thf('15', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.50  thf('16', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['11', '15'])).
% 0.24/0.50  thf('17', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.50      inference('sup-', [status(thm)], ['10', '16'])).
% 0.24/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.24/0.50  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.50  thf('19', plain, ($false), inference('demod', [status(thm)], ['17', '18'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
