%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CYvfj8h0kb

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  192 ( 215 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ ( k1_tarski @ X14 ) )
        = X13 )
      | ( r2_hidden @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k6_subset_1 @ X13 @ ( k1_tarski @ X14 ) )
        = X13 )
      | ( r2_hidden @ X14 @ X13 ) ) ),
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
    ! [X17: $i] :
      ( ( k1_ordinal1 @ X17 )
      = ( k2_xboole_0 @ X17 @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X5 )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X4 @ X5 ) @ X5 )
      = ( k6_subset_1 @ X4 @ X5 ) ) ),
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

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['14','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CYvfj8h0kb
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 25 iterations in 0.015s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(t65_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.47       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ X13 @ (k1_tarski @ X14)) = (X13))
% 0.20/0.47          | (r2_hidden @ X14 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.47  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X15 : $i, X16 : $i]:
% 0.20/0.47         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i]:
% 0.20/0.47         (((k6_subset_1 @ X13 @ (k1_tarski @ X14)) = (X13))
% 0.20/0.47          | (r2_hidden @ X14 @ X13))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf(t52_ordinal1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t52_ordinal1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (((k6_subset_1 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d1_ordinal1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X17 : $i]:
% 0.20/0.47         ((k1_ordinal1 @ X17) = (k2_xboole_0 @ X17 @ (k1_tarski @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.20/0.47  thf(t40_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X5)
% 0.20/0.47           = (k4_xboole_0 @ X4 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X15 : $i, X16 : $i]:
% 0.20/0.47         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X15 : $i, X16 : $i]:
% 0.20/0.47         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         ((k6_subset_1 @ (k2_xboole_0 @ X4 @ X5) @ X5)
% 0.20/0.47           = (k6_subset_1 @ X4 @ X5))),
% 0.20/0.47      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k6_subset_1 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0))
% 0.20/0.47           = (k6_subset_1 @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['4', '8'])).
% 0.20/0.47  thf('10', plain, (((k6_subset_1 @ sk_A @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '9'])).
% 0.20/0.47  thf('11', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_A @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '10'])).
% 0.20/0.47  thf('12', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.20/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.47  thf(t7_ordinal1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X18 : $i, X19 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.47  thf('14', plain, (~ (r1_tarski @ sk_A @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf(d3_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X1 : $i, X3 : $i]:
% 0.20/0.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X1 : $i, X3 : $i]:
% 0.20/0.47         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.47      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.47  thf('19', plain, ($false), inference('demod', [status(thm)], ['14', '18'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
