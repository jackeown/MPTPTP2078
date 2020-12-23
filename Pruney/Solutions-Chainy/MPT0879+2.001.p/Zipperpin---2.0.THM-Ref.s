%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WIiVngznWe

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  57 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  301 ( 475 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t39_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) )
      = ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) )
        = ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) )
 != ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X21 @ X24 ) @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X21 @ X22 ) @ ( k4_tarski @ X21 @ X23 ) @ ( k4_tarski @ X24 @ X22 ) @ ( k4_tarski @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_enumset1 @ ( k4_tarski @ X2 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X1 ) )
      = ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) @ X2 )
      = ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_mcart_1 @ X25 @ X26 @ X27 )
      = ( k4_tarski @ ( k4_tarski @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
 != ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WIiVngznWe
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:50:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 38 iterations in 0.016s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.46  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.46  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.46  thf(t39_mcart_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( k3_zfmisc_1 @
% 0.21/0.46         ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) =
% 0.21/0.46       ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.46        ( ( k3_zfmisc_1 @
% 0.21/0.46            ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) =
% 0.21/0.46          ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t39_mcart_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B) @ 
% 0.21/0.46         (k1_tarski @ sk_C)) != (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t69_enumset1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.46  thf('1', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.46  thf('2', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.46  thf(t146_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 0.21/0.46       ( k2_enumset1 @
% 0.21/0.46         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 0.21/0.46         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.46         ((k2_zfmisc_1 @ (k2_tarski @ X21 @ X24) @ (k2_tarski @ X22 @ X23))
% 0.21/0.46           = (k2_enumset1 @ (k4_tarski @ X21 @ X22) @ 
% 0.21/0.46              (k4_tarski @ X21 @ X23) @ (k4_tarski @ X24 @ X22) @ 
% 0.21/0.46              (k4_tarski @ X24 @ X23)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 0.21/0.46  thf(t71_enumset1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.46         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         ((k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X0 @ X0))
% 0.21/0.46           = (k1_enumset1 @ (k4_tarski @ X2 @ X0) @ (k4_tarski @ X1 @ X0) @ 
% 0.21/0.46              (k4_tarski @ X1 @ X0)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf(t70_enumset1, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X1 : $i, X2 : $i]:
% 0.21/0.46         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.21/0.46      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.46  thf('7', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((k2_zfmisc_1 @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X0 @ X0))
% 0.21/0.46           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['5', '8'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((k2_zfmisc_1 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X1))
% 0.21/0.46           = (k1_tarski @ (k4_tarski @ X0 @ X1)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['2', '9'])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.21/0.46           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['1', '10'])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.21/0.46           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['1', '10'])).
% 0.21/0.46  thf(d3_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.46       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.46         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 0.21/0.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 0.21/0.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         ((k3_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0) @ X2)
% 0.21/0.46           = (k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ X2))),
% 0.21/0.46      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.21/0.46           = (k1_tarski @ (k4_tarski @ (k4_tarski @ X2 @ X1) @ X0)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['11', '14'])).
% 0.21/0.46  thf(d3_mcart_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.46         ((k3_mcart_1 @ X25 @ X26 @ X27)
% 0.21/0.46           = (k4_tarski @ (k4_tarski @ X25 @ X26) @ X27))),
% 0.21/0.46      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.21/0.46           = (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      (((k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))
% 0.21/0.46         != (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '17'])).
% 0.21/0.46  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
