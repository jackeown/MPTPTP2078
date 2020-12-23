%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W6VwKaZha7

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  82 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  153 ( 521 expanded)
%              Number of equality atoms :    5 (  25 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t7_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r2_hidden @ A @ B )
          & ( r1_tarski @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t7_ordinal1])).

thf('0',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference('sup+',[status(thm)],['2','6'])).

thf('9',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference('sup+',[status(thm)],['2','6'])).

thf('10',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference('sup+',[status(thm)],['2','6'])).

thf(t5_ordinal1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ B @ C )
        & ( r2_hidden @ C @ D )
        & ( r2_hidden @ D @ E )
        & ( r2_hidden @ E @ A ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ X16 @ X12 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t5_ordinal1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ sk_A @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference('sup+',[status(thm)],['2','6'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['15','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W6VwKaZha7
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 57 iterations in 0.035s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(t7_ordinal1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t7_ordinal1])).
% 0.21/0.48  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t12_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.48  thf('2', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d3_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.48           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ X3)
% 0.21/0.48          | (r2_hidden @ X0 @ X2)
% 0.21/0.48          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.21/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.48  thf('6', plain, (![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.48  thf('7', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.21/0.48      inference('sup+', [status(thm)], ['2', '6'])).
% 0.21/0.48  thf('8', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.21/0.48      inference('sup+', [status(thm)], ['2', '6'])).
% 0.21/0.48  thf('9', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.21/0.48      inference('sup+', [status(thm)], ['2', '6'])).
% 0.21/0.48  thf('10', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.21/0.48      inference('sup+', [status(thm)], ['2', '6'])).
% 0.21/0.48  thf(t5_ordinal1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.48     ( ~( ( r2_hidden @ A @ B ) & ( r2_hidden @ B @ C ) & 
% 0.21/0.48          ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & ( r2_hidden @ E @ A ) ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X12 @ X13)
% 0.21/0.48          | ~ (r2_hidden @ X13 @ X14)
% 0.21/0.48          | ~ (r2_hidden @ X14 @ X15)
% 0.21/0.48          | ~ (r2_hidden @ X16 @ X12)
% 0.21/0.48          | ~ (r2_hidden @ X15 @ X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [t5_ordinal1])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.48          | ~ (r2_hidden @ X2 @ X1)
% 0.21/0.48          | ~ (r2_hidden @ sk_A @ X2))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ sk_A @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.48          | ~ (r2_hidden @ X1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ sk_A @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '13'])).
% 0.21/0.48  thf('15', plain, (~ (r2_hidden @ sk_A @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '14'])).
% 0.21/0.48  thf('16', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.21/0.48      inference('sup+', [status(thm)], ['2', '6'])).
% 0.21/0.48  thf('17', plain, ($false), inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
