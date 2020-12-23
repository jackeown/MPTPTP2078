%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U8U2omdVdq

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:52 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   53 (  64 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  347 ( 444 expanded)
%              Number of equality atoms :   45 (  58 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k2_tarski @ X28 @ X29 ) @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('11',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['4','9','10'])).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k2_tarski @ X28 @ X29 ) @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ sk_A @ sk_B @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ sk_A @ sk_B @ X0 )
      = ( k2_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

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

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X20 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_tarski @ sk_B @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X13 @ X14 @ X11 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ( X26 = X23 )
      | ( X25
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('24',plain,(
    ! [X23: $i,X26: $i] :
      ( ( X26 = X23 )
      | ~ ( r2_hidden @ X26 @ ( k1_tarski @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U8U2omdVdq
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:28:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 139 iterations in 0.070s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(t21_zfmisc_1, conjecture,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.36/0.54         ( k1_xboole_0 ) ) =>
% 0.36/0.54       ( ( A ) = ( B ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i]:
% 0.36/0.54        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.36/0.54            ( k1_xboole_0 ) ) =>
% 0.36/0.54          ( ( A ) = ( B ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t98_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i]:
% 0.36/0.54         ((k2_xboole_0 @ X7 @ X8)
% 0.36/0.54           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.36/0.54         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['0', '1'])).
% 0.36/0.54  thf(t5_boole, axiom,
% 0.36/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.54  thf('3', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.36/0.54         = (k1_tarski @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.54  thf(t69_enumset1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.54  thf('5', plain, (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.36/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.54  thf(t43_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.36/0.54       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.54         ((k1_enumset1 @ X28 @ X29 @ X30)
% 0.36/0.54           = (k2_xboole_0 @ (k2_tarski @ X28 @ X29) @ (k1_tarski @ X30)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.36/0.54           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.54  thf(t70_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X32 : $i, X33 : $i]:
% 0.36/0.54         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.36/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k2_tarski @ X0 @ X1)
% 0.36/0.54           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.54  thf(commutativity_k2_tarski, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.36/0.54  thf('11', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['4', '9', '10'])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.54         ((k1_enumset1 @ X28 @ X29 @ X30)
% 0.36/0.54           = (k2_xboole_0 @ (k2_tarski @ X28 @ X29) @ (k1_tarski @ X30)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((k1_enumset1 @ sk_A @ sk_B @ X0)
% 0.36/0.54           = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ X0)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['11', '12'])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k2_tarski @ X0 @ X1)
% 0.36/0.54           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (![X0 : $i]: ((k1_enumset1 @ sk_A @ sk_B @ X0) = (k2_tarski @ sk_B @ X0))),
% 0.36/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.54  thf(d1_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.36/0.54       ( ![E:$i]:
% 0.36/0.54         ( ( r2_hidden @ E @ D ) <=>
% 0.36/0.54           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.36/0.54  thf(zf_stmt_2, axiom,
% 0.36/0.54    (![E:$i,C:$i,B:$i,A:$i]:
% 0.36/0.54     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.36/0.54       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_3, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.36/0.54       ( ![E:$i]:
% 0.36/0.54         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.54         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.36/0.54          | (r2_hidden @ X16 @ X20)
% 0.36/0.54          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.54         ((r2_hidden @ X16 @ (k1_enumset1 @ X19 @ X18 @ X17))
% 0.36/0.54          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19))),
% 0.36/0.54      inference('simplify', [status(thm)], ['16'])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r2_hidden @ X1 @ (k2_tarski @ sk_B @ X0))
% 0.36/0.54          | (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['15', '17'])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.54         (((X12) != (X11)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.36/0.54         ~ (zip_tseitin_0 @ X11 @ X13 @ X14 @ X11)),
% 0.36/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.36/0.54  thf('21', plain, (![X0 : $i]: (r2_hidden @ sk_A @ (k2_tarski @ sk_B @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['18', '20'])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.36/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.54  thf(d1_tarski, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.36/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X26 @ X25)
% 0.36/0.54          | ((X26) = (X23))
% 0.36/0.54          | ((X25) != (k1_tarski @ X23)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (![X23 : $i, X26 : $i]:
% 0.36/0.54         (((X26) = (X23)) | ~ (r2_hidden @ X26 @ (k1_tarski @ X23)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['23'])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)) | ((X1) = (X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['22', '24'])).
% 0.36/0.54  thf('26', plain, (((sk_A) = (sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['21', '25'])).
% 0.36/0.54  thf('27', plain, (((sk_A) != (sk_B))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('28', plain, ($false),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
