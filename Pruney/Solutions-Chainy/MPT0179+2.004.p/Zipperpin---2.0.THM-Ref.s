%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HjZjKxAbB3

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    4
%              Number of atoms          :  133 ( 133 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t95_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t95_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k6_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k5_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t80_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k5_enumset1 @ X17 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t80_enumset1])).

thf(t83_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X22 @ X22 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_enumset1])).

thf('4',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf('5',plain,(
    $false ),
    inference(simplify,[status(thm)],['4'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HjZjKxAbB3
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:46:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 4 iterations in 0.007s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.19/0.45                                           $i > $i).
% 0.19/0.45  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.45  thf(t95_enumset1, conjecture,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i,B:$i]:
% 0.19/0.45        ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ B ) =
% 0.19/0.45          ( k2_tarski @ A @ B ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t95_enumset1])).
% 0.19/0.45  thf('0', plain,
% 0.19/0.45      (((k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B)
% 0.19/0.45         != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t75_enumset1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.19/0.45     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.19/0.45       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.45         ((k6_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.19/0.45           = (k5_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16))),
% 0.19/0.45      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.19/0.45  thf(t80_enumset1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.45     ( ( k5_enumset1 @ A @ A @ A @ B @ C @ D @ E ) =
% 0.19/0.45       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.45         ((k5_enumset1 @ X17 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.19/0.45           = (k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.19/0.45      inference('cnf', [status(esa)], [t80_enumset1])).
% 0.19/0.45  thf(t83_enumset1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( k3_enumset1 @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.45  thf('3', plain,
% 0.19/0.45      (![X22 : $i, X23 : $i]:
% 0.19/0.45         ((k3_enumset1 @ X22 @ X22 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.19/0.45      inference('cnf', [status(esa)], [t83_enumset1])).
% 0.19/0.45  thf('4', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.45      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 0.19/0.45  thf('5', plain, ($false), inference('simplify', [status(thm)], ['4'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
