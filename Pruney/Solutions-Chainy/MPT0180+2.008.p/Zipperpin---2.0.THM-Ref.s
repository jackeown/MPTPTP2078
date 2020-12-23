%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gEYF758NY1

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    4
%              Number of atoms          :  102 ( 102 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(t96_enumset1,conjecture,(
    ! [A: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ A )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t96_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t90_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t90_enumset1])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf('5',plain,(
    $false ),
    inference(simplify,[status(thm)],['4'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gEYF758NY1
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 3 iterations in 0.006s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.45                                           $i > $i).
% 0.20/0.45  thf(t96_enumset1, conjecture,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i]:
% 0.20/0.45        ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t96_enumset1])).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (((k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.45         != (k1_tarski @ sk_A))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t90_enumset1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45     ( ( k6_enumset1 @ A @ A @ A @ A @ A @ B @ C @ D ) =
% 0.20/0.45       ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.45         ((k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X4 @ X5 @ X6)
% 0.20/0.45           = (k2_enumset1 @ X3 @ X4 @ X5 @ X6))),
% 0.20/0.45      inference('cnf', [status(esa)], [t90_enumset1])).
% 0.20/0.45  thf(t77_enumset1, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X1 : $i, X2 : $i]:
% 0.20/0.45         ((k2_enumset1 @ X1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.20/0.45      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.20/0.45  thf(t69_enumset1, axiom,
% 0.20/0.45    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.45  thf('3', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.45  thf('4', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 0.20/0.45  thf('5', plain, ($false), inference('simplify', [status(thm)], ['4'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
