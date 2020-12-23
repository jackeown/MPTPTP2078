%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yyJmQxEZHD

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:25 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   26 (  38 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  221 ( 353 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t125_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ D @ C @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t125_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
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
 != ( k2_enumset1 @ sk_D @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t108_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ C @ D ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X5 @ X4 @ X6 @ X7 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t108_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('5',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X5 @ X4 @ X6 @ X7 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t108_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X3 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X3 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X3 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X0 @ X2 @ X3 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['5','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yyJmQxEZHD
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 152 iterations in 0.320s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.77  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.77  thf(t125_enumset1, conjecture,
% 0.58/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.77     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.77        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t125_enumset1])).
% 0.58/0.77  thf('0', plain,
% 0.58/0.77      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.58/0.77         != (k2_enumset1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(t105_enumset1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.77     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 0.58/0.77  thf('1', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.58/0.77      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.58/0.77  thf('2', plain,
% 0.58/0.77      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.58/0.77         != (k2_enumset1 @ sk_D @ sk_A @ sk_C @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['0', '1'])).
% 0.58/0.77  thf(t108_enumset1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.77     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 0.58/0.77  thf('3', plain,
% 0.58/0.77      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.58/0.77         ((k2_enumset1 @ X5 @ X4 @ X6 @ X7) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [t108_enumset1])).
% 0.58/0.77  thf('4', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.58/0.77      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.58/0.77  thf('5', plain,
% 0.58/0.77      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.58/0.77         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.58/0.77      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.58/0.77  thf('6', plain,
% 0.58/0.77      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.58/0.77         ((k2_enumset1 @ X5 @ X4 @ X6 @ X7) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [t108_enumset1])).
% 0.58/0.77  thf('7', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.58/0.77      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.58/0.77  thf('8', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         ((k2_enumset1 @ X2 @ X0 @ X3 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['6', '7'])).
% 0.58/0.77  thf('9', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         ((k2_enumset1 @ X2 @ X0 @ X3 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['6', '7'])).
% 0.58/0.77  thf('10', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.58/0.77      inference('sup+', [status(thm)], ['8', '9'])).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         ((k2_enumset1 @ X2 @ X0 @ X3 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['6', '7'])).
% 0.58/0.77  thf('12', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.58/0.77      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.58/0.77  thf('13', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X0 @ X2 @ X3))),
% 0.58/0.77      inference('sup+', [status(thm)], ['11', '12'])).
% 0.58/0.77  thf('14', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['10', '13'])).
% 0.58/0.77  thf('15', plain,
% 0.58/0.77      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.58/0.77         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.58/0.77      inference('demod', [status(thm)], ['5', '14'])).
% 0.58/0.77  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 0.58/0.77  
% 0.58/0.77  % SZS output end Refutation
% 0.58/0.77  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
