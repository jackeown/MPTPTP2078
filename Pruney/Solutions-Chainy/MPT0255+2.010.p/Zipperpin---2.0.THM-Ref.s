%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UVvKTNTIt8

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:57 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   67 (  75 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  351 ( 393 expanded)
%              Number of equality atoms :   33 (  38 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_xboole_0])).

thf('3',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('5',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['3','4'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','7'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_xboole_0])).

thf('16',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('20',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
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

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X20 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('28',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('29',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_B @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X13 @ X14 @ X11 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    $false ),
    inference('sup-',[status(thm)],['35','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UVvKTNTIt8
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:14:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 323 iterations in 0.168s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.62  thf(t50_zfmisc_1, conjecture,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.62        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(fc5_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.62       ( ~( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) ))).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (![X5 : $i, X6 : $i]:
% 0.38/0.62         ((v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X6 @ X5)))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 0.38/0.62  thf('3', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C_1))),
% 0.38/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.62  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.62  thf('5', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.38/0.62      inference('demod', [status(thm)], ['3', '4'])).
% 0.38/0.62  thf(l13_xboole_0, axiom,
% 0.38/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.62  thf('7', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['0', '7'])).
% 0.38/0.62  thf(commutativity_k2_tarski, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.38/0.62  thf('9', plain,
% 0.38/0.62      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.62  thf(l51_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (![X32 : $i, X33 : $i]:
% 0.38/0.62         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 0.38/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      (![X32 : $i, X33 : $i]:
% 0.38/0.62         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 0.38/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.62  thf('14', plain,
% 0.38/0.62      (((k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['8', '13'])).
% 0.38/0.62  thf('15', plain,
% 0.38/0.62      (![X5 : $i, X6 : $i]:
% 0.38/0.62         ((v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X6 @ X5)))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.62        | (v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.62  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.62  thf('18', plain, ((v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['16', '17'])).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.62  thf('20', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.62  thf(t70_enumset1, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (![X23 : $i, X24 : $i]:
% 0.38/0.62         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.38/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.62  thf(d1_enumset1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.62       ( ![E:$i]:
% 0.38/0.62         ( ( r2_hidden @ E @ D ) <=>
% 0.38/0.62           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.62  thf(zf_stmt_2, axiom,
% 0.38/0.62    (![E:$i,C:$i,B:$i,A:$i]:
% 0.38/0.62     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.38/0.62       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_3, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.62       ( ![E:$i]:
% 0.38/0.62         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.62         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.38/0.62          | (r2_hidden @ X16 @ X20)
% 0.38/0.62          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.62         ((r2_hidden @ X16 @ (k1_enumset1 @ X19 @ X18 @ X17))
% 0.38/0.62          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19))),
% 0.38/0.62      inference('simplify', [status(thm)], ['22'])).
% 0.38/0.62  thf('24', plain,
% 0.38/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.62  thf(t2_boole, axiom,
% 0.38/0.62    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t2_boole])).
% 0.38/0.62  thf(t4_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.38/0.62            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.38/0.62          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.62  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.38/0.62  thf('28', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.38/0.62      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.38/0.62  thf('29', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.38/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['24', '29'])).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.62         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.38/0.62          | ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['23', '30'])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 0.38/0.62          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.38/0.62      inference('sup-', [status(thm)], ['21', '31'])).
% 0.38/0.62  thf('33', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.62          | (zip_tseitin_0 @ X0 @ sk_B @ sk_A @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['20', '32'])).
% 0.38/0.62  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.62  thf('35', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.38/0.62  thf('36', plain,
% 0.38/0.62      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.62         (((X12) != (X11)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.62  thf('37', plain,
% 0.38/0.62      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.38/0.62         ~ (zip_tseitin_0 @ X11 @ X13 @ X14 @ X11)),
% 0.38/0.62      inference('simplify', [status(thm)], ['36'])).
% 0.38/0.62  thf('38', plain, ($false), inference('sup-', [status(thm)], ['35', '37'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
