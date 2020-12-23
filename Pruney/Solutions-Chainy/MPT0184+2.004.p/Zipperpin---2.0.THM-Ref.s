%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pph8jqCcZh

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:02 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   15 (  16 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    5
%              Number of atoms          :   91 ( 100 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t102_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_enumset1 @ A @ B @ C )
        = ( k1_enumset1 @ C @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t102_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_C @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X3 @ X5 @ X4 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('2',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t99_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ A @ C ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X6 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t99_enumset1])).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X3 @ X5 @ X4 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('5',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    $false ),
    inference(simplify,[status(thm)],['5'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pph8jqCcZh
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:33:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.18/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.46  % Solved by: fo/fo7.sh
% 0.18/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.46  % done 3 iterations in 0.015s
% 0.18/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.46  % SZS output start Refutation
% 0.18/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.46  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.18/0.46  thf(t102_enumset1, conjecture,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.18/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.18/0.46        ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ) )),
% 0.18/0.46    inference('cnf.neg', [status(esa)], [t102_enumset1])).
% 0.18/0.46  thf('0', plain,
% 0.18/0.46      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.18/0.46         != (k1_enumset1 @ sk_C @ sk_B @ sk_A))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(t98_enumset1, axiom,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.18/0.46  thf('1', plain,
% 0.18/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.46         ((k1_enumset1 @ X3 @ X5 @ X4) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.18/0.46      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.18/0.46  thf('2', plain,
% 0.18/0.46      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.18/0.46         != (k1_enumset1 @ sk_C @ sk_A @ sk_B))),
% 0.18/0.46      inference('demod', [status(thm)], ['0', '1'])).
% 0.18/0.46  thf(t99_enumset1, axiom,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ))).
% 0.18/0.46  thf('3', plain,
% 0.18/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.18/0.46         ((k1_enumset1 @ X7 @ X6 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.18/0.46      inference('cnf', [status(esa)], [t99_enumset1])).
% 0.18/0.46  thf('4', plain,
% 0.18/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.46         ((k1_enumset1 @ X3 @ X5 @ X4) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.18/0.46      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.18/0.46  thf('5', plain,
% 0.18/0.46      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.18/0.46         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.18/0.46      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.18/0.46  thf('6', plain, ($false), inference('simplify', [status(thm)], ['5'])).
% 0.18/0.46  
% 0.18/0.46  % SZS output end Refutation
% 0.18/0.46  
% 0.18/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
