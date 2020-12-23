%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.okgbIppXAg

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  216 ( 283 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t48_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X19 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r2_hidden @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_C @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('6',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
    = sk_B ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
 != sk_B ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.okgbIppXAg
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:31:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 62 iterations in 0.026s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(t48_zfmisc_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.19/0.47       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.47        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.19/0.47          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.19/0.47  thf('0', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t38_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.19/0.47       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.19/0.47         ((r1_tarski @ (k2_tarski @ X19 @ X21) @ X22)
% 0.19/0.47          | ~ (r2_hidden @ X21 @ X22)
% 0.19/0.47          | ~ (r2_hidden @ X19 @ X22))),
% 0.19/0.47      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X0 @ sk_B)
% 0.19/0.47          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.47  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_C @ sk_A) @ sk_B)),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '3'])).
% 0.19/0.47  thf(commutativity_k2_tarski, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.19/0.47      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.47  thf('6', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.19/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.47  thf(t28_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i]:
% 0.19/0.47         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.19/0.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 0.19/0.47         = (k2_tarski @ sk_A @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))
% 0.19/0.47         = (k2_tarski @ sk_A @ sk_C))),
% 0.19/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf(t22_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X2 : $i, X3 : $i]:
% 0.19/0.47         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)) = (X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)) = (sk_B))),
% 0.19/0.47      inference('sup+', [status(thm)], ['10', '11'])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) != (sk_B))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.19/0.47      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.47  thf(l51_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X17 : $i, X18 : $i]:
% 0.19/0.47         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.19/0.47      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X17 : $i, X18 : $i]:
% 0.19/0.47         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.19/0.47      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('sup+', [status(thm)], ['16', '17'])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)) != (sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['13', '18'])).
% 0.19/0.47  thf('20', plain, ($false),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['12', '19'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
