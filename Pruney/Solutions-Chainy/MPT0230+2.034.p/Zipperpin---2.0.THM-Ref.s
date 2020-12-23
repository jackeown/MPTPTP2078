%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mufTVzbwSD

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:15 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   63 (  75 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  466 ( 586 expanded)
%              Number of equality atoms :   59 (  75 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k3_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,
    ( ( k2_tarski @ sk_B @ sk_C )
    = ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('12',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k2_enumset1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X31 @ X32 @ X33 ) @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('14',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k1_enumset1 @ X63 @ X65 @ X64 )
      = ( k1_enumset1 @ X63 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X30 @ X29 @ X28 )
      = ( k1_enumset1 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('17',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k2_enumset1 @ X38 @ X38 @ X39 @ X40 )
      = ( k1_enumset1 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('21',plain,
    ( ( k2_tarski @ sk_B @ sk_C )
    = ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['10','13','18','19','20'])).

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

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X15 @ X19 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('25',plain,(
    ! [X22: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X24 )
      | ( X26 = X25 )
      | ( X26 = X22 )
      | ( X24
       != ( k2_tarski @ X25 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('26',plain,(
    ! [X22: $i,X25: $i,X26: $i] :
      ( ( X26 = X22 )
      | ( X26 = X25 )
      | ~ ( r2_hidden @ X26 @ ( k2_tarski @ X25 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( X0 = sk_B )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X10 )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('29',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X12 @ X13 @ X10 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mufTVzbwSD
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:29:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.99/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.21  % Solved by: fo/fo7.sh
% 0.99/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.21  % done 1463 iterations in 0.763s
% 0.99/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.21  % SZS output start Refutation
% 0.99/1.21  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.99/1.21  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.99/1.21  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.99/1.21  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.99/1.21  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.99/1.21  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.99/1.21  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.99/1.21  thf(sk_C_type, type, sk_C: $i).
% 0.99/1.21  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.21  thf(t25_zfmisc_1, conjecture,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.99/1.21          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.99/1.21  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.21    (~( ![A:$i,B:$i,C:$i]:
% 0.99/1.21        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.99/1.21             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.99/1.21    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.99/1.21  thf('0', plain,
% 0.99/1.21      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf(t28_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.99/1.21  thf('1', plain,
% 0.99/1.21      (![X8 : $i, X9 : $i]:
% 0.99/1.21         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.99/1.21      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.99/1.21  thf('2', plain,
% 0.99/1.21      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.99/1.21         = (k1_tarski @ sk_A))),
% 0.99/1.21      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.21  thf(commutativity_k3_xboole_0, axiom,
% 0.99/1.21    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.99/1.21  thf('3', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.21  thf(idempotence_k3_xboole_0, axiom,
% 0.99/1.21    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.99/1.21  thf('4', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.99/1.21      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.99/1.21  thf(t23_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.99/1.21       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.99/1.21  thf('5', plain,
% 0.99/1.21      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.99/1.21         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 0.99/1.21           = (k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k3_xboole_0 @ X5 @ X7)))),
% 0.99/1.21      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.99/1.21  thf('6', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.99/1.21           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['4', '5'])).
% 0.99/1.21  thf(t21_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.99/1.21  thf('7', plain,
% 0.99/1.21      (![X3 : $i, X4 : $i]:
% 0.99/1.21         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (X3))),
% 0.99/1.21      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.99/1.21  thf('8', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.99/1.21      inference('demod', [status(thm)], ['6', '7'])).
% 0.99/1.21  thf('9', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['3', '8'])).
% 0.99/1.21  thf('10', plain,
% 0.99/1.21      (((k2_tarski @ sk_B @ sk_C)
% 0.99/1.21         = (k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['2', '9'])).
% 0.99/1.21  thf(t70_enumset1, axiom,
% 0.99/1.21    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.99/1.21  thf('11', plain,
% 0.99/1.21      (![X36 : $i, X37 : $i]:
% 0.99/1.21         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.99/1.21      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.99/1.21  thf(t46_enumset1, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.21     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.99/1.21       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.99/1.21  thf('12', plain,
% 0.99/1.21      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.99/1.21         ((k2_enumset1 @ X31 @ X32 @ X33 @ X34)
% 0.99/1.21           = (k2_xboole_0 @ (k1_enumset1 @ X31 @ X32 @ X33) @ (k1_tarski @ X34)))),
% 0.99/1.21      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.99/1.21  thf('13', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.21         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.99/1.21           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['11', '12'])).
% 0.99/1.21  thf(t98_enumset1, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.99/1.21  thf('14', plain,
% 0.99/1.21      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.99/1.21         ((k1_enumset1 @ X63 @ X65 @ X64) = (k1_enumset1 @ X63 @ X64 @ X65))),
% 0.99/1.21      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.99/1.21  thf(t102_enumset1, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.99/1.21  thf('15', plain,
% 0.99/1.21      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.99/1.21         ((k1_enumset1 @ X30 @ X29 @ X28) = (k1_enumset1 @ X28 @ X29 @ X30))),
% 0.99/1.21      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.99/1.21  thf('16', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.21         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['14', '15'])).
% 0.99/1.21  thf(t71_enumset1, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.99/1.21  thf('17', plain,
% 0.99/1.21      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.99/1.21         ((k2_enumset1 @ X38 @ X38 @ X39 @ X40)
% 0.99/1.21           = (k1_enumset1 @ X38 @ X39 @ X40))),
% 0.99/1.21      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.99/1.21  thf('18', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.21         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['16', '17'])).
% 0.99/1.21  thf('19', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.21         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['14', '15'])).
% 0.99/1.21  thf('20', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.21         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['14', '15'])).
% 0.99/1.21  thf('21', plain,
% 0.99/1.21      (((k2_tarski @ sk_B @ sk_C) = (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.99/1.21      inference('demod', [status(thm)], ['10', '13', '18', '19', '20'])).
% 0.99/1.21  thf(d1_enumset1, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.21     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.99/1.21       ( ![E:$i]:
% 0.99/1.21         ( ( r2_hidden @ E @ D ) <=>
% 0.99/1.21           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.99/1.21  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.99/1.21  thf(zf_stmt_2, axiom,
% 0.99/1.21    (![E:$i,C:$i,B:$i,A:$i]:
% 0.99/1.21     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.99/1.21       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.99/1.21  thf(zf_stmt_3, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.21     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.99/1.21       ( ![E:$i]:
% 0.99/1.21         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.99/1.21  thf('22', plain,
% 0.99/1.21      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.99/1.21         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.99/1.21          | (r2_hidden @ X15 @ X19)
% 0.99/1.21          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.99/1.21  thf('23', plain,
% 0.99/1.21      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.99/1.21         ((r2_hidden @ X15 @ (k1_enumset1 @ X18 @ X17 @ X16))
% 0.99/1.21          | (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 0.99/1.21      inference('simplify', [status(thm)], ['22'])).
% 0.99/1.21  thf('24', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.99/1.21          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A))),
% 0.99/1.21      inference('sup+', [status(thm)], ['21', '23'])).
% 0.99/1.21  thf(d2_tarski, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.99/1.21       ( ![D:$i]:
% 0.99/1.21         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.99/1.21  thf('25', plain,
% 0.99/1.21      (![X22 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.99/1.21         (~ (r2_hidden @ X26 @ X24)
% 0.99/1.21          | ((X26) = (X25))
% 0.99/1.21          | ((X26) = (X22))
% 0.99/1.21          | ((X24) != (k2_tarski @ X25 @ X22)))),
% 0.99/1.21      inference('cnf', [status(esa)], [d2_tarski])).
% 0.99/1.21  thf('26', plain,
% 0.99/1.21      (![X22 : $i, X25 : $i, X26 : $i]:
% 0.99/1.21         (((X26) = (X22))
% 0.99/1.21          | ((X26) = (X25))
% 0.99/1.21          | ~ (r2_hidden @ X26 @ (k2_tarski @ X25 @ X22)))),
% 0.99/1.21      inference('simplify', [status(thm)], ['25'])).
% 0.99/1.21  thf('27', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A)
% 0.99/1.21          | ((X0) = (sk_B))
% 0.99/1.21          | ((X0) = (sk_C)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['24', '26'])).
% 0.99/1.21  thf('28', plain,
% 0.99/1.21      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.99/1.21         (((X11) != (X10)) | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X10))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.99/1.21  thf('29', plain,
% 0.99/1.21      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.99/1.21         ~ (zip_tseitin_0 @ X10 @ X12 @ X13 @ X10)),
% 0.99/1.21      inference('simplify', [status(thm)], ['28'])).
% 0.99/1.21  thf('30', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['27', '29'])).
% 0.99/1.21  thf('31', plain, (((sk_A) != (sk_B))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('32', plain, (((sk_A) != (sk_C))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('33', plain, ($false),
% 0.99/1.22      inference('simplify_reflect-', [status(thm)], ['30', '31', '32'])).
% 0.99/1.22  
% 0.99/1.22  % SZS output end Refutation
% 0.99/1.22  
% 0.99/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
