%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3jdAbPWEFU

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:48 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   38 (  50 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  238 ( 400 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t14_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ B )
          & ! [D: $i] :
              ( ( ( r1_tarski @ A @ D )
                & ( r1_tarski @ C @ D ) )
             => ( r1_tarski @ B @ D ) ) )
       => ( B
          = ( k2_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_xboole_1])).

thf('4',plain,(
    ! [X9: $i] :
      ( ( r1_tarski @ sk_B @ X9 )
      | ~ ( r1_tarski @ sk_C @ X9 )
      | ~ ( r1_tarski @ sk_A @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) )
      | ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C ) )
    = ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['10','23'])).

thf('25',plain,(
    sk_B
 != ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3jdAbPWEFU
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:56:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 159 iterations in 0.096s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(commutativity_k2_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.55  thf(t7_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['0', '1'])).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.36/0.55  thf(t14_xboole_1, conjecture,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 0.36/0.55         ( ![D:$i]:
% 0.36/0.55           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 0.36/0.55             ( r1_tarski @ B @ D ) ) ) ) =>
% 0.36/0.55       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.55        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 0.36/0.55            ( ![D:$i]:
% 0.36/0.55              ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 0.36/0.55                ( r1_tarski @ B @ D ) ) ) ) =>
% 0.36/0.55          ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t14_xboole_1])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X9 : $i]:
% 0.36/0.55         ((r1_tarski @ sk_B @ X9)
% 0.36/0.55          | ~ (r1_tarski @ sk_C @ X9)
% 0.36/0.55          | ~ (r1_tarski @ sk_A @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C @ X0))
% 0.36/0.55          | (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.55  thf('6', plain, ((r1_tarski @ sk_B @ (k2_xboole_0 @ sk_C @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['2', '5'])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.55  thf('8', plain, ((r1_tarski @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.36/0.55  thf(t12_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i]:
% 0.36/0.55         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C))
% 0.36/0.55         = (k2_xboole_0 @ sk_A @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf('11', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i]:
% 0.36/0.55         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.55  thf('13', plain, (((k2_xboole_0 @ sk_C @ sk_B) = (sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.55  thf('15', plain, (((k2_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.55  thf('16', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t9_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( r1_tarski @ A @ B ) =>
% 0.36/0.55       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X6 @ X7)
% 0.36/0.55          | (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ (k2_xboole_0 @ X7 @ X8)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t9_xboole_1])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ (k2_xboole_0 @ sk_B @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.55  thf('19', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.36/0.55      inference('sup+', [status(thm)], ['15', '18'])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i]:
% 0.36/0.55         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (((k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B) = (sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C)) = (sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.36/0.55  thf('24', plain, (((k2_xboole_0 @ sk_A @ sk_C) = (sk_B))),
% 0.36/0.55      inference('sup+', [status(thm)], ['10', '23'])).
% 0.36/0.55  thf('25', plain, (((sk_B) != (k2_xboole_0 @ sk_A @ sk_C))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('26', plain, ($false),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
