%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S6faNQL12F

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:23 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   37 (  52 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  213 ( 384 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k3_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('15',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('21',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S6faNQL12F
% 0.13/0.36  % Computer   : n019.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 15:11:38 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 26 iterations in 0.019s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.49  thf(t77_xboole_1, conjecture,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.23/0.49          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.49        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.23/0.49             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.23/0.49  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t4_xboole_0, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      (![X2 : $i, X3 : $i]:
% 0.23/0.49         ((r1_xboole_0 @ X2 @ X3)
% 0.23/0.49          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.23/0.49  thf('2', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X2 : $i, X3 : $i]:
% 0.23/0.49         ((r1_xboole_0 @ X2 @ X3)
% 0.23/0.49          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.23/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.23/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.23/0.49  thf('4', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.23/0.49          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.23/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.23/0.49          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.23/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.49  thf('7', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.23/0.49      inference('sup-', [status(thm)], ['3', '6'])).
% 0.23/0.49  thf('8', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.23/0.49      inference('sup-', [status(thm)], ['2', '7'])).
% 0.23/0.49  thf('9', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t28_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.23/0.49  thf('10', plain,
% 0.23/0.49      (![X9 : $i, X10 : $i]:
% 0.23/0.49         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.23/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.23/0.49  thf('11', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.49  thf('12', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.23/0.49  thf('13', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 0.23/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.23/0.49  thf(t16_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.23/0.49       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.23/0.49  thf('14', plain,
% 0.23/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.49         ((k3_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8)
% 0.23/0.49           = (k3_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.23/0.49  thf('15', plain,
% 0.23/0.49      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.23/0.49          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.23/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.23/0.49  thf('16', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.23/0.49          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.49  thf('17', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ sk_A))
% 0.23/0.49          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_1) @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['13', '16'])).
% 0.23/0.49  thf('18', plain,
% 0.23/0.49      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['8', '17'])).
% 0.23/0.49  thf('19', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.23/0.49      inference('sup-', [status(thm)], ['1', '18'])).
% 0.23/0.49  thf('20', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.23/0.49      inference('sup-', [status(thm)], ['3', '6'])).
% 0.23/0.49  thf('21', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.23/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.49  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
