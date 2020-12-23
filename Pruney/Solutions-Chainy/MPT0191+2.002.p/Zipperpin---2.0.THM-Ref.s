%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LHmeAGrBSK

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    4
%              Number of atoms          :   67 (  67 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t110_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ C @ A @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ B @ C @ A @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t110_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l123_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ C @ A @ D ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l123_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    $false ),
    inference(simplify,[status(thm)],['2'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LHmeAGrBSK
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:36:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 1 iterations in 0.005s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(t110_enumset1, conjecture,
% 0.22/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.46     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ C @ A @ D ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.46        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ C @ A @ D ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t110_enumset1])).
% 0.22/0.46  thf('0', plain,
% 0.22/0.46      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.22/0.46         != (k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_D))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(l123_enumset1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.46     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ C @ A @ D ) ))).
% 0.22/0.46  thf('1', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.46         ((k2_enumset1 @ X2 @ X0 @ X1 @ X3) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.22/0.46      inference('cnf', [status(esa)], [l123_enumset1])).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.22/0.46         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.46      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.46  thf('3', plain, ($false), inference('simplify', [status(thm)], ['2'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
