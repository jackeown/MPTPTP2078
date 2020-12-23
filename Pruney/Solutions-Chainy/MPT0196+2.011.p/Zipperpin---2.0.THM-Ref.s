%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sW6K1spICx

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:18 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   21 (  25 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  166 ( 210 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t117_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ B @ D @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ C @ B @ D @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t117_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_C @ sk_B @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_C @ sk_A @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t116_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ B @ A @ D ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X10 @ X9 @ X8 @ X11 )
      = ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t116_enumset1])).

thf('4',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X10 @ X9 @ X8 @ X11 )
      = ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t116_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X3 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('10',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['4','7','8','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sW6K1spICx
% 0.15/0.38  % Computer   : n001.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 20:33:15 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.25/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.54  % Solved by: fo/fo7.sh
% 0.25/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.54  % done 23 iterations in 0.083s
% 0.25/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.54  % SZS output start Refutation
% 0.25/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.25/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.25/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.54  thf(t117_enumset1, conjecture,
% 0.25/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ D @ A ) ))).
% 0.25/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.54        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ D @ A ) ) )),
% 0.25/0.54    inference('cnf.neg', [status(esa)], [t117_enumset1])).
% 0.25/0.54  thf('0', plain,
% 0.25/0.54      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.25/0.54         != (k2_enumset1 @ sk_C @ sk_B @ sk_D @ sk_A))),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf(t105_enumset1, axiom,
% 0.25/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 0.25/0.54  thf('1', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.54         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.25/0.54      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.25/0.54  thf('2', plain,
% 0.25/0.54      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.25/0.54         != (k2_enumset1 @ sk_C @ sk_A @ sk_B @ sk_D))),
% 0.25/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.25/0.54  thf(t116_enumset1, axiom,
% 0.25/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ A @ D ) ))).
% 0.25/0.54  thf('3', plain,
% 0.25/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.25/0.54         ((k2_enumset1 @ X10 @ X9 @ X8 @ X11)
% 0.25/0.54           = (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 0.25/0.54      inference('cnf', [status(esa)], [t116_enumset1])).
% 0.25/0.54  thf('4', plain,
% 0.25/0.54      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.25/0.54         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 0.25/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.25/0.54  thf('5', plain,
% 0.25/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.25/0.54         ((k2_enumset1 @ X10 @ X9 @ X8 @ X11)
% 0.25/0.54           = (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 0.25/0.54      inference('cnf', [status(esa)], [t116_enumset1])).
% 0.25/0.54  thf('6', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.54         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.25/0.54      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.25/0.54  thf('7', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.54         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X3 @ X0 @ X2))),
% 0.25/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.25/0.54  thf('8', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.54         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.25/0.54      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.25/0.54  thf('9', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.54         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.25/0.54      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.25/0.54  thf('10', plain,
% 0.25/0.54      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.25/0.54         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.25/0.54      inference('demod', [status(thm)], ['4', '7', '8', '9'])).
% 0.25/0.54  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.25/0.54  
% 0.25/0.54  % SZS output end Refutation
% 0.25/0.54  
% 0.25/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
