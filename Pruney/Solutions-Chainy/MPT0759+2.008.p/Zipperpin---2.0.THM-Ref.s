%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jqNNe2ajt4

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:18 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  133 ( 133 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( k1_ordinal1 @ X7 )
      = ( k2_xboole_0 @ X7 @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t141_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X3 @ ( k1_tarski @ X4 ) ) @ ( k1_tarski @ X4 ) )
        = X3 )
      | ( r2_hidden @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t141_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r2_hidden @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t52_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t52_ordinal1])).

thf('3',plain,(
    ( k6_subset_1 @ ( k1_ordinal1 @ sk_A ) @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(simplify,[status(thm)],['6'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('9',plain,(
    ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['9','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jqNNe2ajt4
% 0.15/0.37  % Computer   : n003.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 10:20:42 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.49  % Solved by: fo/fo7.sh
% 0.24/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.49  % done 10 iterations in 0.010s
% 0.24/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.49  % SZS output start Refutation
% 0.24/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.49  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.24/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.49  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.24/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.49  thf(d1_ordinal1, axiom,
% 0.24/0.49    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.24/0.49  thf('0', plain,
% 0.24/0.49      (![X7 : $i]: ((k1_ordinal1 @ X7) = (k2_xboole_0 @ X7 @ (k1_tarski @ X7)))),
% 0.24/0.49      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.24/0.49  thf(t141_zfmisc_1, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( ~( r2_hidden @ A @ B ) ) =>
% 0.24/0.49       ( ( k4_xboole_0 @
% 0.24/0.49           ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.24/0.49         ( B ) ) ))).
% 0.24/0.49  thf('1', plain,
% 0.24/0.49      (![X3 : $i, X4 : $i]:
% 0.24/0.49         (((k4_xboole_0 @ (k2_xboole_0 @ X3 @ (k1_tarski @ X4)) @ 
% 0.24/0.49            (k1_tarski @ X4)) = (X3))
% 0.24/0.49          | (r2_hidden @ X4 @ X3))),
% 0.24/0.49      inference('cnf', [status(esa)], [t141_zfmisc_1])).
% 0.24/0.49  thf('2', plain,
% 0.24/0.49      (![X0 : $i]:
% 0.24/0.49         (((k4_xboole_0 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0)) = (X0))
% 0.24/0.49          | (r2_hidden @ X0 @ X0))),
% 0.24/0.49      inference('sup+', [status(thm)], ['0', '1'])).
% 0.24/0.49  thf(t52_ordinal1, conjecture,
% 0.24/0.49    (![A:$i]:
% 0.24/0.49     ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.24/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.49    (~( ![A:$i]:
% 0.24/0.49        ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.24/0.49    inference('cnf.neg', [status(esa)], [t52_ordinal1])).
% 0.24/0.49  thf('3', plain,
% 0.24/0.49      (((k6_subset_1 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(redefinition_k6_subset_1, axiom,
% 0.24/0.49    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.24/0.49  thf('4', plain,
% 0.24/0.49      (![X5 : $i, X6 : $i]: ((k6_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))),
% 0.24/0.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.24/0.49  thf('5', plain,
% 0.24/0.49      (((k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.24/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.24/0.49  thf('6', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_A @ sk_A))),
% 0.24/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.24/0.49  thf('7', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.24/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.24/0.49  thf(t7_ordinal1, axiom,
% 0.24/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.49  thf('8', plain,
% 0.24/0.49      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.24/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.24/0.49  thf('9', plain, (~ (r1_tarski @ sk_A @ sk_A)),
% 0.24/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.49  thf(d10_xboole_0, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.49  thf('10', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.24/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.49  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.24/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.24/0.49  thf('12', plain, ($false), inference('demod', [status(thm)], ['9', '11'])).
% 0.24/0.49  
% 0.24/0.49  % SZS output end Refutation
% 0.24/0.49  
% 0.24/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
