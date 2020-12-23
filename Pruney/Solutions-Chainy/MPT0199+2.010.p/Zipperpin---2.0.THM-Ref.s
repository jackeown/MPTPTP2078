%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J0acZ67jkM

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   18 (  21 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  133 ( 166 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t123_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ B @ C @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ D @ B @ C @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t123_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_D @ sk_B @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_D @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t113_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X7 @ X4 @ X6 @ X5 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X7 @ X4 @ X6 @ X5 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('7',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    $false ),
    inference(simplify,[status(thm)],['7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J0acZ67jkM
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:04:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 3 iterations in 0.010s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.46  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.46  thf(t123_enumset1, conjecture,
% 0.22/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.46     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ B @ C @ A ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.46        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ B @ C @ A ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t123_enumset1])).
% 0.22/0.46  thf('0', plain,
% 0.22/0.46      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.22/0.46         != (k2_enumset1 @ sk_D @ sk_B @ sk_C @ sk_A))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(t107_enumset1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.46     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.22/0.46  thf('1', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.46         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.22/0.46      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.22/0.46         != (k2_enumset1 @ sk_D @ sk_A @ sk_C @ sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.46  thf(t113_enumset1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.46     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 0.22/0.46  thf('3', plain,
% 0.22/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.46         ((k2_enumset1 @ X7 @ X4 @ X6 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.22/0.46      inference('cnf', [status(esa)], [t113_enumset1])).
% 0.22/0.46  thf('4', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.46         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.22/0.46      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.22/0.46  thf('5', plain,
% 0.22/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.46         ((k2_enumset1 @ X7 @ X4 @ X6 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.22/0.46      inference('cnf', [status(esa)], [t113_enumset1])).
% 0.22/0.46  thf('6', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.46         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.22/0.46      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.22/0.46         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.46      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.22/0.46  thf('8', plain, ($false), inference('simplify', [status(thm)], ['7'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
