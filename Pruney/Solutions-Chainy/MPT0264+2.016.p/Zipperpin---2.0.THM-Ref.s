%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Iln0FYl2R6

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:40 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   54 (  62 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  393 ( 499 expanded)
%              Number of equality atoms :   38 (  52 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( X13 = X14 )
      | ( X13 = X15 )
      | ( X13 = X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('1',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X17 @ X21 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X14 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['13','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X18 @ X19 @ X20 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X18 @ X19 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Iln0FYl2R6
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:32:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.96  % Solved by: fo/fo7.sh
% 0.75/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.96  % done 953 iterations in 0.543s
% 0.75/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.96  % SZS output start Refutation
% 0.75/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.75/0.96  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.75/0.96  thf(d1_enumset1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.96       ( ![E:$i]:
% 0.75/0.96         ( ( r2_hidden @ E @ D ) <=>
% 0.75/0.96           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_0, axiom,
% 0.75/0.96    (![E:$i,C:$i,B:$i,A:$i]:
% 0.75/0.96     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.75/0.96       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.75/0.96  thf('0', plain,
% 0.75/0.96      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.75/0.96         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.75/0.96          | ((X13) = (X14))
% 0.75/0.96          | ((X13) = (X15))
% 0.75/0.96          | ((X13) = (X16)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(t59_zfmisc_1, conjecture,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.75/0.96          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_1, negated_conjecture,
% 0.75/0.96    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.96        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.75/0.96             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 0.75/0.96    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 0.75/0.96  thf('1', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.96  thf(d5_xboole_0, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.75/0.96       ( ![D:$i]:
% 0.75/0.96         ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.96           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.75/0.96  thf('2', plain,
% 0.75/0.96      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X2 @ X3)
% 0.75/0.96          | (r2_hidden @ X2 @ X4)
% 0.75/0.96          | (r2_hidden @ X2 @ X5)
% 0.75/0.96          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.96      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.96  thf('3', plain,
% 0.75/0.96      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.96         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.75/0.96          | (r2_hidden @ X2 @ X4)
% 0.75/0.96          | ~ (r2_hidden @ X2 @ X3))),
% 0.75/0.96      inference('simplify', [status(thm)], ['2'])).
% 0.75/0.96  thf('4', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((r2_hidden @ sk_B @ X0)
% 0.75/0.96          | (r2_hidden @ sk_B @ (k4_xboole_0 @ sk_C @ X0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['1', '3'])).
% 0.75/0.96  thf('5', plain,
% 0.75/0.96      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.96  thf(commutativity_k3_xboole_0, axiom,
% 0.75/0.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/0.96  thf('6', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.96  thf('7', plain,
% 0.75/0.96      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_tarski @ sk_A))),
% 0.75/0.96      inference('demod', [status(thm)], ['5', '6'])).
% 0.75/0.96  thf(t47_xboole_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.75/0.96  thf('8', plain,
% 0.75/0.96      (![X8 : $i, X9 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.75/0.96           = (k4_xboole_0 @ X8 @ X9))),
% 0.75/0.96      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.75/0.96  thf('9', plain,
% 0.75/0.96      (((k4_xboole_0 @ sk_C @ (k1_tarski @ sk_A))
% 0.75/0.96         = (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.75/0.96      inference('sup+', [status(thm)], ['7', '8'])).
% 0.75/0.96  thf('10', plain,
% 0.75/0.96      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X6 @ X5)
% 0.75/0.96          | ~ (r2_hidden @ X6 @ X4)
% 0.75/0.96          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.96      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.96  thf('11', plain,
% 0.75/0.96      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X6 @ X4)
% 0.75/0.96          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.96      inference('simplify', [status(thm)], ['10'])).
% 0.75/0.96  thf('12', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))
% 0.75/0.96          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['9', '11'])).
% 0.75/0.96  thf('13', plain,
% 0.75/0.96      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.75/0.96        | ~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['4', '12'])).
% 0.75/0.96  thf(t70_enumset1, axiom,
% 0.75/0.96    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.75/0.96  thf('14', plain,
% 0.75/0.96      (![X25 : $i, X26 : $i]:
% 0.75/0.96         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.75/0.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.96  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.75/0.96  thf(zf_stmt_3, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.96       ( ![E:$i]:
% 0.75/0.96         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.75/0.96  thf('15', plain,
% 0.75/0.96      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.75/0.96         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.75/0.96          | (r2_hidden @ X17 @ X21)
% 0.75/0.96          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.96  thf('16', plain,
% 0.75/0.96      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.75/0.96         ((r2_hidden @ X17 @ (k1_enumset1 @ X20 @ X19 @ X18))
% 0.75/0.96          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20))),
% 0.75/0.96      inference('simplify', [status(thm)], ['15'])).
% 0.75/0.96  thf('17', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.75/0.96          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.96      inference('sup+', [status(thm)], ['14', '16'])).
% 0.75/0.96  thf('18', plain,
% 0.75/0.96      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.96         (((X13) != (X14)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('19', plain,
% 0.75/0.96      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.75/0.96         ~ (zip_tseitin_0 @ X14 @ X14 @ X15 @ X12)),
% 0.75/0.96      inference('simplify', [status(thm)], ['18'])).
% 0.75/0.96  thf('20', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.75/0.96      inference('sup-', [status(thm)], ['17', '19'])).
% 0.75/0.96  thf('21', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.75/0.96      inference('demod', [status(thm)], ['13', '20'])).
% 0.75/0.96  thf(t69_enumset1, axiom,
% 0.75/0.96    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.75/0.96  thf('22', plain,
% 0.75/0.96      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.75/0.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.96  thf('23', plain,
% 0.75/0.96      (![X25 : $i, X26 : $i]:
% 0.75/0.96         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.75/0.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.96  thf('24', plain,
% 0.75/0.96      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X22 @ X21)
% 0.75/0.96          | ~ (zip_tseitin_0 @ X22 @ X18 @ X19 @ X20)
% 0.75/0.96          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.96  thf('25', plain,
% 0.75/0.96      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i]:
% 0.75/0.96         (~ (zip_tseitin_0 @ X22 @ X18 @ X19 @ X20)
% 0.75/0.96          | ~ (r2_hidden @ X22 @ (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.75/0.96      inference('simplify', [status(thm)], ['24'])).
% 0.75/0.96  thf('26', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.75/0.96          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.96      inference('sup-', [status(thm)], ['23', '25'])).
% 0.75/0.96  thf('27', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.75/0.96          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['22', '26'])).
% 0.75/0.96  thf('28', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 0.75/0.96      inference('sup-', [status(thm)], ['21', '27'])).
% 0.75/0.96  thf('29', plain,
% 0.75/0.96      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['0', '28'])).
% 0.75/0.96  thf('30', plain, (((sk_B) = (sk_A))),
% 0.75/0.96      inference('simplify', [status(thm)], ['29'])).
% 0.75/0.96  thf('31', plain, (((sk_A) != (sk_B))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.96  thf('32', plain, ($false),
% 0.75/0.96      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.75/0.96  
% 0.75/0.96  % SZS output end Refutation
% 0.75/0.96  
% 0.75/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
