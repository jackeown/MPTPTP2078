%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L0AcY3xX48

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:54 EST 2020

% Result     : Theorem 3.12s
% Output     : Refutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  253 ( 356 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t27_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = sk_C ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k3_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C )
      = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C )
      = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k3_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k3_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['11','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L0AcY3xX48
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 3.12/3.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.12/3.31  % Solved by: fo/fo7.sh
% 3.12/3.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.12/3.31  % done 1494 iterations in 2.864s
% 3.12/3.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.12/3.31  % SZS output start Refutation
% 3.12/3.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.12/3.31  thf(sk_D_type, type, sk_D: $i).
% 3.12/3.31  thf(sk_A_type, type, sk_A: $i).
% 3.12/3.31  thf(sk_C_type, type, sk_C: $i).
% 3.12/3.31  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.12/3.31  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.12/3.31  thf(sk_B_type, type, sk_B: $i).
% 3.12/3.31  thf(t27_xboole_1, conjecture,
% 3.12/3.31    (![A:$i,B:$i,C:$i,D:$i]:
% 3.12/3.31     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 3.12/3.31       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ))).
% 3.12/3.31  thf(zf_stmt_0, negated_conjecture,
% 3.12/3.31    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.12/3.31        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 3.12/3.31          ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )),
% 3.12/3.31    inference('cnf.neg', [status(esa)], [t27_xboole_1])).
% 3.12/3.31  thf('0', plain,
% 3.12/3.31      (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ (k3_xboole_0 @ sk_B @ sk_D))),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf(commutativity_k3_xboole_0, axiom,
% 3.12/3.31    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.12/3.31  thf('1', plain,
% 3.12/3.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.12/3.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.12/3.31  thf('2', plain, ((r1_tarski @ sk_C @ sk_D)),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf(t12_xboole_1, axiom,
% 3.12/3.31    (![A:$i,B:$i]:
% 3.12/3.31     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.12/3.31  thf('3', plain,
% 3.12/3.31      (![X2 : $i, X3 : $i]:
% 3.12/3.31         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 3.12/3.31      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.12/3.31  thf('4', plain, (((k2_xboole_0 @ sk_C @ sk_D) = (sk_D))),
% 3.12/3.31      inference('sup-', [status(thm)], ['2', '3'])).
% 3.12/3.31  thf(t21_xboole_1, axiom,
% 3.12/3.31    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 3.12/3.31  thf('5', plain,
% 3.12/3.31      (![X9 : $i, X10 : $i]:
% 3.12/3.31         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 3.12/3.31      inference('cnf', [status(esa)], [t21_xboole_1])).
% 3.12/3.31  thf('6', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (sk_C))),
% 3.12/3.31      inference('sup+', [status(thm)], ['4', '5'])).
% 3.12/3.31  thf(t16_xboole_1, axiom,
% 3.12/3.31    (![A:$i,B:$i,C:$i]:
% 3.12/3.31     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 3.12/3.31       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 3.12/3.31  thf('7', plain,
% 3.12/3.31      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.12/3.31         ((k3_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ X6)
% 3.12/3.31           = (k3_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 3.12/3.31      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.12/3.31  thf('8', plain,
% 3.12/3.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.12/3.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.12/3.31  thf('9', plain,
% 3.12/3.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.12/3.31         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 3.12/3.31           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.12/3.31      inference('sup+', [status(thm)], ['7', '8'])).
% 3.12/3.31  thf('10', plain,
% 3.12/3.31      (![X0 : $i]:
% 3.12/3.31         ((k3_xboole_0 @ X0 @ sk_C)
% 3.12/3.31           = (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_D @ X0)))),
% 3.12/3.31      inference('sup+', [status(thm)], ['6', '9'])).
% 3.12/3.31  thf('11', plain,
% 3.12/3.31      (![X0 : $i]:
% 3.12/3.31         ((k3_xboole_0 @ X0 @ sk_C)
% 3.12/3.31           = (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ X0 @ sk_D)))),
% 3.12/3.31      inference('sup+', [status(thm)], ['1', '10'])).
% 3.12/3.31  thf('12', plain, ((r1_tarski @ sk_A @ sk_B)),
% 3.12/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.31  thf('13', plain,
% 3.12/3.31      (![X2 : $i, X3 : $i]:
% 3.12/3.31         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 3.12/3.31      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.12/3.31  thf('14', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 3.12/3.31      inference('sup-', [status(thm)], ['12', '13'])).
% 3.12/3.31  thf('15', plain,
% 3.12/3.31      (![X9 : $i, X10 : $i]:
% 3.12/3.31         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 3.12/3.31      inference('cnf', [status(esa)], [t21_xboole_1])).
% 3.12/3.31  thf('16', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 3.12/3.31      inference('sup+', [status(thm)], ['14', '15'])).
% 3.12/3.31  thf('17', plain,
% 3.12/3.31      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.12/3.31         ((k3_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ X6)
% 3.12/3.31           = (k3_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 3.12/3.31      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.12/3.31  thf('18', plain,
% 3.12/3.31      (![X0 : $i]:
% 3.12/3.31         ((k3_xboole_0 @ sk_A @ X0)
% 3.12/3.31           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 3.12/3.31      inference('sup+', [status(thm)], ['16', '17'])).
% 3.12/3.31  thf('19', plain,
% 3.12/3.31      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.12/3.31         ((k3_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ X6)
% 3.12/3.31           = (k3_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 3.12/3.31      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.12/3.31  thf('20', plain,
% 3.12/3.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.12/3.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.12/3.31  thf(t17_xboole_1, axiom,
% 3.12/3.31    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 3.12/3.31  thf('21', plain,
% 3.12/3.31      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 3.12/3.31      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.12/3.31  thf('22', plain,
% 3.12/3.31      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 3.12/3.31      inference('sup+', [status(thm)], ['20', '21'])).
% 3.12/3.31  thf('23', plain,
% 3.12/3.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.12/3.31         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)),
% 3.12/3.31      inference('sup+', [status(thm)], ['19', '22'])).
% 3.12/3.31  thf('24', plain,
% 3.12/3.31      (![X0 : $i, X1 : $i]:
% 3.12/3.31         (r1_tarski @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ sk_A @ X0)) @ 
% 3.12/3.31          (k3_xboole_0 @ sk_B @ X0))),
% 3.12/3.31      inference('sup+', [status(thm)], ['18', '23'])).
% 3.12/3.31  thf('25', plain,
% 3.12/3.31      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ (k3_xboole_0 @ sk_B @ sk_D))),
% 3.12/3.31      inference('sup+', [status(thm)], ['11', '24'])).
% 3.12/3.31  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 3.12/3.31  
% 3.12/3.31  % SZS output end Refutation
% 3.12/3.31  
% 3.12/3.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
