%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CCiN0BkSmn

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:39 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   48 (  52 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  325 ( 381 expanded)
%              Number of equality atoms :   32 (  40 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf('0',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X11 ) )
      | ( r2_hidden @ X8 @ X11 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X16 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['11','18'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('20',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( X29 = X26 )
      | ( X28
       != ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('21',plain,(
    ! [X26: $i,X29: $i] :
      ( ( X29 = X26 )
      | ~ ( r2_hidden @ X29 @ ( k1_tarski @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CCiN0BkSmn
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.84/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.84/1.03  % Solved by: fo/fo7.sh
% 0.84/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.03  % done 1112 iterations in 0.581s
% 0.84/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.84/1.03  % SZS output start Refutation
% 0.84/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.84/1.03  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.84/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.84/1.03  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.84/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.84/1.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.84/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.84/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.03  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.84/1.03  thf(t59_zfmisc_1, conjecture,
% 0.84/1.03    (![A:$i,B:$i,C:$i]:
% 0.84/1.03     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.84/1.03          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 0.84/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.03    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.03        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.84/1.03             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 0.84/1.03    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 0.84/1.03  thf('0', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(t1_xboole_0, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i]:
% 0.84/1.03     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.84/1.03       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.84/1.03  thf('1', plain,
% 0.84/1.03      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.84/1.03         ((r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X11))
% 0.84/1.03          | (r2_hidden @ X8 @ X11)
% 0.84/1.03          | ~ (r2_hidden @ X8 @ X9))),
% 0.84/1.03      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.84/1.03  thf('2', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         ((r2_hidden @ sk_B @ X0)
% 0.84/1.03          | (r2_hidden @ sk_B @ (k5_xboole_0 @ sk_C_1 @ X0)))),
% 0.84/1.03      inference('sup-', [status(thm)], ['0', '1'])).
% 0.84/1.03  thf('3', plain,
% 0.84/1.03      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_tarski @ sk_A))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(commutativity_k3_xboole_0, axiom,
% 0.84/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.84/1.03  thf('4', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.03  thf('5', plain,
% 0.84/1.03      (((k3_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (k1_tarski @ sk_A))),
% 0.84/1.03      inference('demod', [status(thm)], ['3', '4'])).
% 0.84/1.03  thf(t100_xboole_1, axiom,
% 0.84/1.03    (![A:$i,B:$i]:
% 0.84/1.03     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.84/1.03  thf('6', plain,
% 0.84/1.03      (![X12 : $i, X13 : $i]:
% 0.84/1.03         ((k4_xboole_0 @ X12 @ X13)
% 0.84/1.03           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.84/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.84/1.03  thf('7', plain,
% 0.84/1.03      (((k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.84/1.03         = (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.84/1.03      inference('sup+', [status(thm)], ['5', '6'])).
% 0.84/1.03  thf(d5_xboole_0, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i]:
% 0.84/1.03     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.84/1.03       ( ![D:$i]:
% 0.84/1.03         ( ( r2_hidden @ D @ C ) <=>
% 0.84/1.03           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.84/1.03  thf('8', plain,
% 0.84/1.03      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.84/1.03         (~ (r2_hidden @ X6 @ X5)
% 0.84/1.03          | ~ (r2_hidden @ X6 @ X4)
% 0.84/1.03          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.84/1.03      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.84/1.03  thf('9', plain,
% 0.84/1.03      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.84/1.03         (~ (r2_hidden @ X6 @ X4)
% 0.84/1.03          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.84/1.03      inference('simplify', [status(thm)], ['8'])).
% 0.84/1.03  thf('10', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         (~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)))
% 0.84/1.03          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.03      inference('sup-', [status(thm)], ['7', '9'])).
% 0.84/1.03  thf('11', plain,
% 0.84/1.03      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.84/1.03        | ~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.03      inference('sup-', [status(thm)], ['2', '10'])).
% 0.84/1.03  thf(t70_enumset1, axiom,
% 0.84/1.03    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.84/1.03  thf('12', plain,
% 0.84/1.03      (![X32 : $i, X33 : $i]:
% 0.84/1.03         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.84/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.84/1.03  thf(d1_enumset1, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.84/1.03       ( ![E:$i]:
% 0.84/1.03         ( ( r2_hidden @ E @ D ) <=>
% 0.84/1.03           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.84/1.03  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.84/1.03  thf(zf_stmt_2, axiom,
% 0.84/1.03    (![E:$i,C:$i,B:$i,A:$i]:
% 0.84/1.03     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.84/1.03       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.84/1.03  thf(zf_stmt_3, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.84/1.03       ( ![E:$i]:
% 0.84/1.03         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.84/1.03  thf('13', plain,
% 0.84/1.03      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.84/1.03         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 0.84/1.03          | (r2_hidden @ X19 @ X23)
% 0.84/1.03          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.84/1.03  thf('14', plain,
% 0.84/1.03      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.84/1.03         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 0.84/1.03          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 0.84/1.03      inference('simplify', [status(thm)], ['13'])).
% 0.84/1.03  thf('15', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.03         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.84/1.03          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.84/1.03      inference('sup+', [status(thm)], ['12', '14'])).
% 0.84/1.03  thf('16', plain,
% 0.84/1.03      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.84/1.03         (((X15) != (X16)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.84/1.03  thf('17', plain,
% 0.84/1.03      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.84/1.03         ~ (zip_tseitin_0 @ X16 @ X16 @ X17 @ X14)),
% 0.84/1.03      inference('simplify', [status(thm)], ['16'])).
% 0.84/1.03  thf('18', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.84/1.03      inference('sup-', [status(thm)], ['15', '17'])).
% 0.84/1.03  thf('19', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.84/1.03      inference('demod', [status(thm)], ['11', '18'])).
% 0.84/1.03  thf(d1_tarski, axiom,
% 0.84/1.03    (![A:$i,B:$i]:
% 0.84/1.03     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.84/1.03       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.84/1.03  thf('20', plain,
% 0.84/1.03      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.84/1.03         (~ (r2_hidden @ X29 @ X28)
% 0.84/1.03          | ((X29) = (X26))
% 0.84/1.03          | ((X28) != (k1_tarski @ X26)))),
% 0.84/1.03      inference('cnf', [status(esa)], [d1_tarski])).
% 0.84/1.03  thf('21', plain,
% 0.84/1.03      (![X26 : $i, X29 : $i]:
% 0.84/1.03         (((X29) = (X26)) | ~ (r2_hidden @ X29 @ (k1_tarski @ X26)))),
% 0.84/1.03      inference('simplify', [status(thm)], ['20'])).
% 0.84/1.03  thf('22', plain, (((sk_B) = (sk_A))),
% 0.84/1.03      inference('sup-', [status(thm)], ['19', '21'])).
% 0.84/1.03  thf('23', plain, (((sk_A) != (sk_B))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('24', plain, ($false),
% 0.84/1.03      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.84/1.03  
% 0.84/1.03  % SZS output end Refutation
% 0.84/1.03  
% 0.84/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
