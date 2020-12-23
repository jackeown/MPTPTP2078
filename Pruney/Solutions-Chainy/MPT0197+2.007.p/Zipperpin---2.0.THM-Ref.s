%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0gW8XShHz5

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:19 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  221 ( 265 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t118_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ D @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ C @ D @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t118_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_C @ sk_D @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X7 @ X6 @ X5 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_C @ sk_B @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t113_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X11 @ X8 @ X10 @ X9 )
      = ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X7 @ X6 @ X5 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('5',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(t117_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ B @ D @ A ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X15 @ X13 @ X12 @ X14 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t117_enumset1])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('8',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X7 @ X6 @ X5 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('13',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['8','11','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0gW8XShHz5
% 0.16/0.38  % Computer   : n018.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 11:42:57 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.24/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.54  % Solved by: fo/fo7.sh
% 0.24/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.54  % done 12 iterations in 0.044s
% 0.24/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.54  % SZS output start Refutation
% 0.24/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.24/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.54  thf(t118_enumset1, conjecture,
% 0.24/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ A @ B ) ))).
% 0.24/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.54        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ A @ B ) ) )),
% 0.24/0.54    inference('cnf.neg', [status(esa)], [t118_enumset1])).
% 0.24/0.54  thf('0', plain,
% 0.24/0.54      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.54         != (k2_enumset1 @ sk_C @ sk_D @ sk_A @ sk_B))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(t107_enumset1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.24/0.54  thf('1', plain,
% 0.24/0.54      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.54         ((k2_enumset1 @ X4 @ X7 @ X6 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.24/0.54      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.24/0.54  thf('2', plain,
% 0.24/0.54      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.54         != (k2_enumset1 @ sk_C @ sk_B @ sk_A @ sk_D))),
% 0.24/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.24/0.54  thf(t113_enumset1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 0.24/0.54  thf('3', plain,
% 0.24/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.24/0.54         ((k2_enumset1 @ X11 @ X8 @ X10 @ X9)
% 0.24/0.54           = (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 0.24/0.54      inference('cnf', [status(esa)], [t113_enumset1])).
% 0.24/0.54  thf('4', plain,
% 0.24/0.54      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.54         ((k2_enumset1 @ X4 @ X7 @ X6 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.24/0.54      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.24/0.54  thf('5', plain,
% 0.24/0.54      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.54         != (k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_D))),
% 0.24/0.54      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.24/0.54  thf(t117_enumset1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ D @ A ) ))).
% 0.24/0.54  thf('6', plain,
% 0.24/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.24/0.54         ((k2_enumset1 @ X15 @ X13 @ X12 @ X14)
% 0.24/0.54           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 0.24/0.54      inference('cnf', [status(esa)], [t117_enumset1])).
% 0.24/0.54  thf(t103_enumset1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 0.24/0.54  thf('7', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.54         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.24/0.54      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.24/0.54  thf('8', plain,
% 0.24/0.54      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.54         != (k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D))),
% 0.24/0.54      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.24/0.54  thf('9', plain,
% 0.24/0.54      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.54         ((k2_enumset1 @ X4 @ X7 @ X6 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.24/0.54      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.24/0.54  thf('10', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.54         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.24/0.54      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.24/0.54  thf('11', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.54         ((k2_enumset1 @ X3 @ X0 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.24/0.54      inference('sup+', [status(thm)], ['9', '10'])).
% 0.24/0.54  thf('12', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.54         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.24/0.54      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.24/0.54  thf('13', plain,
% 0.24/0.54      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.54         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.24/0.54      inference('demod', [status(thm)], ['8', '11', '12'])).
% 0.24/0.54  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.24/0.54  
% 0.24/0.54  % SZS output end Refutation
% 0.24/0.54  
% 0.24/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
