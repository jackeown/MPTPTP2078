%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VfDLrQ86Fn

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:39 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   56 (  63 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  385 ( 468 expanded)
%              Number of equality atoms :   43 (  54 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X21 @ X21 @ X22 @ X23 )
      = ( k1_enumset1 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X14 @ X15 @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r2_hidden @ X39 @ X40 )
      | ( ( k3_xboole_0 @ X40 @ ( k1_tarski @ X39 ) )
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
       != ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','12'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('14',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k3_xboole_0 @ X42 @ ( k1_tarski @ X41 ) )
        = ( k1_tarski @ X41 ) )
      | ~ ( r2_hidden @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k3_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k3_xboole_0 @ X42 @ ( k1_tarski @ X41 ) )
        = ( k1_tarski @ X41 ) )
      | ~ ( r2_hidden @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r2_hidden @ X39 @ X40 )
      | ( ( k3_xboole_0 @ X40 @ ( k1_tarski @ X39 ) )
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_B )
     != ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['27'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( X12 = X9 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('30',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VfDLrQ86Fn
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.79  % Solved by: fo/fo7.sh
% 0.58/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.79  % done 371 iterations in 0.342s
% 0.58/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.79  % SZS output start Refutation
% 0.58/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.58/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.79  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.58/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.79  thf(t70_enumset1, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.58/0.79  thf('0', plain,
% 0.58/0.79      (![X19 : $i, X20 : $i]:
% 0.58/0.79         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.58/0.79      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.79  thf(t71_enumset1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.58/0.79  thf('1', plain,
% 0.58/0.79      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.79         ((k2_enumset1 @ X21 @ X21 @ X22 @ X23)
% 0.58/0.79           = (k1_enumset1 @ X21 @ X22 @ X23))),
% 0.58/0.79      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.58/0.79  thf(t46_enumset1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.79     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.58/0.79       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.58/0.79  thf('2', plain,
% 0.58/0.79      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.79         ((k2_enumset1 @ X14 @ X15 @ X16 @ X17)
% 0.58/0.79           = (k2_xboole_0 @ (k1_enumset1 @ X14 @ X15 @ X16) @ (k1_tarski @ X17)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.58/0.79  thf(commutativity_k2_xboole_0, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.58/0.79  thf('3', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.79  thf(t21_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.58/0.79  thf('4', plain,
% 0.58/0.79      (![X7 : $i, X8 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (X7))),
% 0.58/0.79      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.58/0.79  thf('5', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['3', '4'])).
% 0.58/0.79  thf(commutativity_k3_xboole_0, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.58/0.79  thf('6', plain,
% 0.58/0.79      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.58/0.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.79  thf(l29_zfmisc_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.58/0.79       ( r2_hidden @ B @ A ) ))).
% 0.58/0.79  thf('7', plain,
% 0.58/0.79      (![X39 : $i, X40 : $i]:
% 0.58/0.79         ((r2_hidden @ X39 @ X40)
% 0.58/0.79          | ((k3_xboole_0 @ X40 @ (k1_tarski @ X39)) != (k1_tarski @ X39)))),
% 0.58/0.79      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.58/0.79  thf('8', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) != (k1_tarski @ X1))
% 0.58/0.79          | (r2_hidden @ X1 @ X0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['6', '7'])).
% 0.58/0.79  thf('9', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.58/0.79          | (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['5', '8'])).
% 0.58/0.79  thf('10', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['9'])).
% 0.58/0.79  thf('11', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.79         (r2_hidden @ X0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['2', '10'])).
% 0.58/0.79  thf('12', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['1', '11'])).
% 0.58/0.79  thf('13', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['0', '12'])).
% 0.58/0.79  thf(l31_zfmisc_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( r2_hidden @ A @ B ) =>
% 0.58/0.79       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.58/0.79  thf('14', plain,
% 0.58/0.79      (![X41 : $i, X42 : $i]:
% 0.58/0.79         (((k3_xboole_0 @ X42 @ (k1_tarski @ X41)) = (k1_tarski @ X41))
% 0.58/0.79          | ~ (r2_hidden @ X41 @ X42))),
% 0.58/0.79      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.58/0.79  thf('15', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 0.58/0.79           = (k1_tarski @ X0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.79  thf(t59_zfmisc_1, conjecture,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.58/0.79          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 0.58/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.79        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.58/0.79             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 0.58/0.79    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 0.58/0.79  thf('16', plain,
% 0.58/0.79      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_tarski @ sk_A))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('17', plain,
% 0.58/0.79      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.58/0.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.79  thf('18', plain,
% 0.58/0.79      (((k3_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (k1_tarski @ sk_A))),
% 0.58/0.79      inference('demod', [status(thm)], ['16', '17'])).
% 0.58/0.79  thf(t16_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.58/0.79       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.58/0.79  thf('19', plain,
% 0.58/0.79      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ X6)
% 0.58/0.79           = (k3_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.58/0.79  thf('20', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.58/0.79           = (k3_xboole_0 @ sk_C_1 @ 
% 0.58/0.79              (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['18', '19'])).
% 0.58/0.79  thf('21', plain,
% 0.58/0.79      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.58/0.79         = (k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['15', '20'])).
% 0.58/0.79  thf('22', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('23', plain,
% 0.58/0.79      (![X41 : $i, X42 : $i]:
% 0.58/0.79         (((k3_xboole_0 @ X42 @ (k1_tarski @ X41)) = (k1_tarski @ X41))
% 0.58/0.79          | ~ (r2_hidden @ X41 @ X42))),
% 0.58/0.79      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.58/0.79  thf('24', plain,
% 0.58/0.79      (((k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.58/0.79      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.79  thf('25', plain,
% 0.58/0.79      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.58/0.79         = (k1_tarski @ sk_B))),
% 0.58/0.79      inference('demod', [status(thm)], ['21', '24'])).
% 0.58/0.79  thf('26', plain,
% 0.58/0.79      (![X39 : $i, X40 : $i]:
% 0.58/0.79         ((r2_hidden @ X39 @ X40)
% 0.58/0.79          | ((k3_xboole_0 @ X40 @ (k1_tarski @ X39)) != (k1_tarski @ X39)))),
% 0.58/0.79      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.58/0.79  thf('27', plain,
% 0.58/0.79      ((((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.58/0.79        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.79  thf('28', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.58/0.79      inference('simplify', [status(thm)], ['27'])).
% 0.58/0.79  thf(d1_tarski, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.58/0.79       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.58/0.79  thf('29', plain,
% 0.58/0.79      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X12 @ X11)
% 0.58/0.79          | ((X12) = (X9))
% 0.58/0.79          | ((X11) != (k1_tarski @ X9)))),
% 0.58/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.58/0.79  thf('30', plain,
% 0.58/0.79      (![X9 : $i, X12 : $i]:
% 0.58/0.79         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['29'])).
% 0.58/0.79  thf('31', plain, (((sk_B) = (sk_A))),
% 0.58/0.79      inference('sup-', [status(thm)], ['28', '30'])).
% 0.58/0.79  thf('32', plain, (((sk_A) != (sk_B))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('33', plain, ($false),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.58/0.79  
% 0.58/0.79  % SZS output end Refutation
% 0.58/0.79  
% 0.58/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
