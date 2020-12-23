%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AwMYxsQ4HU

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:20 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   58 (  77 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  371 ( 530 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

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
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('15',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ ( k3_xboole_0 @ X8 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t27_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','19'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ X1 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['3','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['23','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AwMYxsQ4HU
% 0.14/0.37  % Computer   : n011.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 20:37:57 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.70/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.88  % Solved by: fo/fo7.sh
% 0.70/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.88  % done 995 iterations in 0.392s
% 0.70/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.88  % SZS output start Refutation
% 0.70/0.88  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.70/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.88  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.70/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.70/0.88  thf(t77_xboole_1, conjecture,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.70/0.88          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.70/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.88    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.88        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.70/0.88             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.70/0.88    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.70/0.88  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(symmetry_r1_xboole_0, axiom,
% 0.70/0.88    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.70/0.88  thf('2', plain,
% 0.70/0.88      (![X2 : $i, X3 : $i]:
% 0.70/0.88         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.70/0.88      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.70/0.88  thf('3', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.70/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.88  thf(commutativity_k3_xboole_0, axiom,
% 0.70/0.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.70/0.88  thf('4', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.88  thf('5', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.88  thf(t48_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.70/0.88  thf('6', plain,
% 0.70/0.88      (![X16 : $i, X17 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.70/0.88           = (k3_xboole_0 @ X16 @ X17))),
% 0.70/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.88  thf(t36_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.70/0.88  thf('7', plain,
% 0.70/0.88      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.70/0.88      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.70/0.88  thf('8', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.70/0.88      inference('sup+', [status(thm)], ['6', '7'])).
% 0.70/0.88  thf('9', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.70/0.88      inference('sup+', [status(thm)], ['5', '8'])).
% 0.70/0.88  thf(t28_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.70/0.88  thf('10', plain,
% 0.70/0.88      (![X12 : $i, X13 : $i]:
% 0.70/0.88         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.70/0.88      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.88  thf('11', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.70/0.88           = (k3_xboole_0 @ X1 @ X0))),
% 0.70/0.88      inference('sup-', [status(thm)], ['9', '10'])).
% 0.70/0.88  thf('12', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.88  thf('13', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.70/0.88           = (k3_xboole_0 @ X1 @ X0))),
% 0.70/0.88      inference('demod', [status(thm)], ['11', '12'])).
% 0.70/0.88  thf('14', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.70/0.88      inference('sup+', [status(thm)], ['6', '7'])).
% 0.70/0.88  thf('15', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(t27_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.88     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.70/0.88       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ))).
% 0.70/0.88  thf('16', plain,
% 0.70/0.88      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.70/0.88         (~ (r1_tarski @ X8 @ X9)
% 0.70/0.88          | ~ (r1_tarski @ X10 @ X11)
% 0.70/0.88          | (r1_tarski @ (k3_xboole_0 @ X8 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t27_xboole_1])).
% 0.70/0.88  thf('17', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((r1_tarski @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_C_1 @ X0))
% 0.70/0.88          | ~ (r1_tarski @ X1 @ X0))),
% 0.70/0.88      inference('sup-', [status(thm)], ['15', '16'])).
% 0.70/0.88  thf('18', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         (r1_tarski @ (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.70/0.88          (k3_xboole_0 @ sk_C_1 @ X0))),
% 0.70/0.88      inference('sup-', [status(thm)], ['14', '17'])).
% 0.70/0.88  thf('19', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ sk_C_1 @ X0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['13', '18'])).
% 0.70/0.88  thf('20', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.70/0.88      inference('sup+', [status(thm)], ['4', '19'])).
% 0.70/0.88  thf(t63_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.70/0.88       ( r1_xboole_0 @ A @ C ) ))).
% 0.70/0.88  thf('21', plain,
% 0.70/0.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.70/0.88         (~ (r1_tarski @ X18 @ X19)
% 0.70/0.88          | ~ (r1_xboole_0 @ X19 @ X20)
% 0.70/0.88          | (r1_xboole_0 @ X18 @ X20))),
% 0.70/0.88      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.70/0.88  thf('22', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ X1)
% 0.70/0.88          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_1) @ X1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['20', '21'])).
% 0.70/0.88  thf('23', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_A)),
% 0.70/0.88      inference('sup-', [status(thm)], ['3', '22'])).
% 0.70/0.88  thf('24', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.88  thf(t4_xboole_0, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.70/0.88            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.70/0.88       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.70/0.88            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.70/0.88  thf('25', plain,
% 0.70/0.88      (![X4 : $i, X5 : $i]:
% 0.70/0.88         ((r1_xboole_0 @ X4 @ X5)
% 0.70/0.88          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.70/0.88  thf('26', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.70/0.88      inference('sup+', [status(thm)], ['6', '7'])).
% 0.70/0.88  thf('27', plain,
% 0.70/0.88      (![X12 : $i, X13 : $i]:
% 0.70/0.88         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.70/0.88      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.88  thf('28', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.70/0.88           = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['26', '27'])).
% 0.70/0.88  thf('29', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.88  thf('30', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.70/0.88           = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.88      inference('demod', [status(thm)], ['28', '29'])).
% 0.70/0.88  thf('31', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.88  thf('32', plain,
% 0.70/0.88      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.70/0.88          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.70/0.88      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.70/0.88  thf('33', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.70/0.88          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['31', '32'])).
% 0.70/0.88  thf('34', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.70/0.88          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['30', '33'])).
% 0.70/0.88  thf('35', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((r1_xboole_0 @ X1 @ X0)
% 0.70/0.88          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['25', '34'])).
% 0.70/0.88  thf('36', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.70/0.88          | (r1_xboole_0 @ X0 @ X1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['24', '35'])).
% 0.70/0.88  thf('37', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.70/0.88      inference('sup-', [status(thm)], ['23', '36'])).
% 0.70/0.88  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 0.70/0.88  
% 0.70/0.88  % SZS output end Refutation
% 0.70/0.88  
% 0.74/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
