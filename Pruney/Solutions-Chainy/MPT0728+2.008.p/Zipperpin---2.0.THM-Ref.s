%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dyNXMaXAGj

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:39 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  128 ( 128 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t10_ordinal1,conjecture,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t10_ordinal1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( ( k1_ordinal1 @ X14 )
      = ( k2_xboole_0 @ X14 @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ ( k2_tarski @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dyNXMaXAGj
% 0.15/0.38  % Computer   : n024.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 09:35:51 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 17 iterations in 0.012s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.50  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.23/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.50  thf(t10_ordinal1, conjecture,
% 0.23/0.50    (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t10_ordinal1])).
% 0.23/0.50  thf('0', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(d1_ordinal1, axiom,
% 0.23/0.50    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X14 : $i]:
% 0.23/0.50         ((k1_ordinal1 @ X14) = (k2_xboole_0 @ X14 @ (k1_tarski @ X14)))),
% 0.23/0.50      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.23/0.50  thf(t69_enumset1, axiom,
% 0.23/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.23/0.50  thf('2', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.23/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.50  thf(d10_xboole_0, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.23/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.50  thf('4', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.23/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.23/0.50  thf(t38_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.23/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.23/0.50         ((r2_hidden @ X10 @ X11)
% 0.23/0.50          | ~ (r1_tarski @ (k2_tarski @ X10 @ X12) @ X11))),
% 0.23/0.50      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.50  thf('7', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.23/0.50      inference('sup+', [status(thm)], ['2', '6'])).
% 0.23/0.50  thf(d3_xboole_0, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.23/0.50       ( ![D:$i]:
% 0.23/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.23/0.50           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.23/0.50  thf('8', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.23/0.50          | (r2_hidden @ X0 @ X2)
% 0.23/0.50          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.23/0.50      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.23/0.50         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.23/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['7', '9'])).
% 0.23/0.50  thf('11', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.23/0.50      inference('sup+', [status(thm)], ['1', '10'])).
% 0.23/0.50  thf('12', plain, ($false), inference('demod', [status(thm)], ['0', '11'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
