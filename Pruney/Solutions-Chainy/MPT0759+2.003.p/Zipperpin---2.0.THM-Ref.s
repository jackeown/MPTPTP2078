%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bVU2cqqmmP

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  53 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  161 ( 328 expanded)
%              Number of equality atoms :   18 (  40 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ ( k1_tarski @ X12 ) )
        = X11 )
      | ( r2_hidden @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k6_subset_1 @ X11 @ ( k1_tarski @ X12 ) )
        = X11 )
      | ( r2_hidden @ X12 @ X11 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ( k1_ordinal1 @ X15 )
      = ( k2_xboole_0 @ X15 @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X3 )
      = ( k4_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k6_subset_1 @ X13 @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X2 @ X3 ) @ X3 )
      = ( k6_subset_1 @ X2 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k6_subset_1 @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    ( k6_subset_1 @ sk_A @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['3','9'])).

thf('11',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(simplify,[status(thm)],['11'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(simplify,[status(thm)],['11'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bVU2cqqmmP
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.22/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 21 iterations in 0.016s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(t65_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.22/0.50       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i]:
% 0.22/0.50         (((k4_xboole_0 @ X11 @ (k1_tarski @ X12)) = (X11))
% 0.22/0.50          | (r2_hidden @ X12 @ X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.50  thf(redefinition_k6_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i]:
% 0.22/0.50         (((k6_subset_1 @ X11 @ (k1_tarski @ X12)) = (X11))
% 0.22/0.50          | (r2_hidden @ X12 @ X11))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf(t52_ordinal1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t52_ordinal1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (((k6_subset_1 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d1_ordinal1, axiom,
% 0.22/0.50    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X15 : $i]:
% 0.22/0.50         ((k1_ordinal1 @ X15) = (k2_xboole_0 @ X15 @ (k1_tarski @ X15)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.22/0.50  thf(t40_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X3)
% 0.22/0.50           = (k4_xboole_0 @ X2 @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         ((k6_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         ((k6_subset_1 @ (k2_xboole_0 @ X2 @ X3) @ X3)
% 0.22/0.50           = (k6_subset_1 @ X2 @ X3))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k6_subset_1 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0))
% 0.22/0.50           = (k6_subset_1 @ X0 @ (k1_tarski @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['4', '8'])).
% 0.22/0.50  thf('10', plain, (((k6_subset_1 @ sk_A @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['3', '9'])).
% 0.22/0.50  thf('11', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_A @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '10'])).
% 0.22/0.50  thf('12', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.22/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.50  thf(antisymmetry_r2_hidden, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.22/0.50  thf('14', plain, (~ (r2_hidden @ sk_A @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf('15', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.22/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.50  thf('16', plain, ($false), inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
