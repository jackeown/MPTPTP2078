%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o4uKSBVqP8

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  22 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :  177 ( 177 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t90_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k6_enumset1 @ A @ A @ A @ A @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ B @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t90_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k6_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k5_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k5_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_enumset1 @ X4 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('5',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1','2','3','4'])).

thf('6',plain,(
    $false ),
    inference(simplify,[status(thm)],['5'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o4uKSBVqP8
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 4 iterations in 0.009s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.46                                           $i > $i).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.46  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.46  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.46  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.46  thf(t90_enumset1, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( k6_enumset1 @ A @ A @ A @ A @ A @ B @ C @ D ) =
% 0.20/0.46       ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46        ( ( k6_enumset1 @ A @ A @ A @ A @ A @ B @ C @ D ) =
% 0.20/0.46          ( k2_enumset1 @ A @ B @ C @ D ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t90_enumset1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (((k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.46         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t75_enumset1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.46     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.46       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.46         ((k6_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.20/0.46           = (k5_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.20/0.46      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.20/0.46  thf(t74_enumset1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.46     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.46       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.46         ((k5_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.20/0.46           = (k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.20/0.46      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.20/0.46  thf(t73_enumset1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.46     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.20/0.46       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.46         ((k4_enumset1 @ X4 @ X4 @ X5 @ X6 @ X7 @ X8)
% 0.20/0.46           = (k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.20/0.46  thf(t72_enumset1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X3)
% 0.20/0.46           = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.46         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '1', '2', '3', '4'])).
% 0.20/0.46  thf('6', plain, ($false), inference('simplify', [status(thm)], ['5'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
