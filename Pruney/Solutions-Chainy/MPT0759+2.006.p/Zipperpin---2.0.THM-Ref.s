%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1s6bHbIdi5

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  157 ( 164 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( k1_ordinal1 @ X8 )
      = ( k2_xboole_0 @ X8 @ ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t141_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k1_tarski @ X3 ) ) @ ( k1_tarski @ X3 ) )
        = X2 )
      | ( r2_hidden @ X3 @ X2 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
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

thf(t46_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ X4 )
        = X4 )
      | ~ ( r2_hidden @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k1_ordinal1 @ X8 )
      = ( k2_xboole_0 @ X8 @ ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('12',plain,
    ( ( k1_ordinal1 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(t14_ordinal1,axiom,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( X9
     != ( k1_ordinal1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t14_ordinal1])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1s6bHbIdi5
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 9 iterations in 0.010s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(d1_ordinal1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X8 : $i]: ((k1_ordinal1 @ X8) = (k2_xboole_0 @ X8 @ (k1_tarski @ X8)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.21/0.47  thf(t141_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ~( r2_hidden @ A @ B ) ) =>
% 0.21/0.47       ( ( k4_xboole_0 @
% 0.21/0.47           ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.21/0.47         ( B ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         (((k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k1_tarski @ X3)) @ 
% 0.21/0.47            (k1_tarski @ X3)) = (X2))
% 0.21/0.47          | (r2_hidden @ X3 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [t141_zfmisc_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k4_xboole_0 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0)) = (X0))
% 0.21/0.47          | (r2_hidden @ X0 @ X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf(t52_ordinal1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t52_ordinal1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (((k6_subset_1 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (((k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_A @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.47  thf('7', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.21/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.47  thf(t46_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.47       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         (((k2_xboole_0 @ (k1_tarski @ X5) @ X4) = (X4))
% 0.21/0.47          | ~ (r2_hidden @ X5 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 0.21/0.47  thf('9', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_A) = (sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X8 : $i]: ((k1_ordinal1 @ X8) = (k2_xboole_0 @ X8 @ (k1_tarski @ X8)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.21/0.47  thf('12', plain, (((k1_ordinal1 @ sk_A) = (sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.47  thf(t14_ordinal1, axiom, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.21/0.47  thf('13', plain, (![X9 : $i]: ((X9) != (k1_ordinal1 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [t14_ordinal1])).
% 0.21/0.47  thf('14', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
