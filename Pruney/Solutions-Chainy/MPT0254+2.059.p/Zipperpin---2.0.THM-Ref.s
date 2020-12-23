%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jAmjtAY9HR

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  84 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  187 ( 560 expanded)
%              Number of equality atoms :   17 (  57 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
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
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ( r2_hidden @ X17 @ X18 )
      | ( X18
       != ( k2_tarski @ X19 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('5',plain,(
    ! [X16: $i,X19: $i] :
      ( r2_hidden @ X16 @ ( k2_tarski @ X19 @ X16 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ~ ( r2_hidden @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['16','17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jAmjtAY9HR
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:56:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 20 iterations in 0.014s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(t49_zfmisc_1, conjecture,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i]:
% 0.22/0.47        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.22/0.47      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.47  thf(t69_enumset1, axiom,
% 0.22/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.47  thf('3', plain, (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.22/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.47  thf(d2_tarski, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.47       ( ![D:$i]:
% 0.22/0.47         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.47         (((X17) != (X16))
% 0.22/0.47          | (r2_hidden @ X17 @ X18)
% 0.22/0.47          | ((X18) != (k2_tarski @ X19 @ X16)))),
% 0.22/0.47      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X16 : $i, X19 : $i]: (r2_hidden @ X16 @ (k2_tarski @ X19 @ X16))),
% 0.22/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.47  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.47      inference('sup+', [status(thm)], ['3', '5'])).
% 0.22/0.47  thf(d3_xboole_0, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.22/0.47       ( ![D:$i]:
% 0.22/0.47         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.47           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X2 @ X3)
% 0.22/0.47          | (r2_hidden @ X2 @ X4)
% 0.22/0.47          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.22/0.47      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.22/0.47         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.22/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['6', '8'])).
% 0.22/0.47  thf('10', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.22/0.47      inference('sup+', [status(thm)], ['2', '9'])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.22/0.47         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.22/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.47  thf(t1_boole, axiom,
% 0.22/0.47    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.47  thf('13', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.22/0.47      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.47  thf('14', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.22/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.47  thf(t1_xboole_0, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.22/0.47       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X8 @ X9)
% 0.22/0.47          | ~ (r2_hidden @ X8 @ X10)
% 0.22/0.47          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.22/0.47  thf('16', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (~ (r2_hidden @ sk_A @ X0) | ~ (r2_hidden @ sk_A @ X1))),
% 0.22/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('17', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.22/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.47  thf('18', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.22/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.47  thf('19', plain, ($false),
% 0.22/0.47      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
