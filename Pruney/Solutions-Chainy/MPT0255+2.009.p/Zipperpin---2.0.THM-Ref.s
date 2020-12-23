%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tXLrhW8Rl9

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 (  45 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  242 ( 250 expanded)
%              Number of equality atoms :   23 (  24 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','5'])).

thf(fc5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_xboole_0])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
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

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X12 @ X16 )
      | ( X16
       != ( k1_enumset1 @ X15 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k1_enumset1 @ X15 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_B_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X7 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X9 @ X10 @ X7 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    $false ),
    inference('sup-',[status(thm)],['17','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tXLrhW8Rl9
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:00:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 133 iterations in 0.064s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.19/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.51  thf(t50_zfmisc_1, conjecture,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.51        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C) = (k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(commutativity_k2_tarski, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.19/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.51  thf(l51_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X28 : $i, X29 : $i]:
% 0.19/0.51         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 0.19/0.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (![X28 : $i, X29 : $i]:
% 0.19/0.51         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 0.19/0.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.19/0.51      inference('demod', [status(thm)], ['0', '5'])).
% 0.19/0.51  thf(fc5_xboole_0, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.51       ( ~( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) ))).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X3 : $i, X4 : $i]:
% 0.19/0.51         ((v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.51        | (v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.51  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.51  thf('10', plain, ((v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1))),
% 0.19/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.51  thf(t70_enumset1, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      (![X19 : $i, X20 : $i]:
% 0.19/0.51         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.19/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.51  thf(d1_enumset1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.19/0.51       ( ![E:$i]:
% 0.19/0.51         ( ( r2_hidden @ E @ D ) <=>
% 0.19/0.51           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.19/0.51  thf(zf_stmt_2, axiom,
% 0.19/0.51    (![E:$i,C:$i,B:$i,A:$i]:
% 0.19/0.51     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.19/0.51       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_3, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.19/0.51       ( ![E:$i]:
% 0.19/0.51         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.51         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.19/0.51          | (r2_hidden @ X12 @ X16)
% 0.19/0.51          | ((X16) != (k1_enumset1 @ X15 @ X14 @ X13)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.51         ((r2_hidden @ X12 @ (k1_enumset1 @ X15 @ X14 @ X13))
% 0.19/0.51          | (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 0.19/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.51  thf(d1_xboole_0, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.51         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.19/0.51          | ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 0.19/0.51          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['11', '15'])).
% 0.19/0.51  thf('17', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ sk_B_1 @ sk_A @ sk_A)),
% 0.19/0.51      inference('sup-', [status(thm)], ['10', '16'])).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.51         (((X8) != (X7)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X7 : $i, X9 : $i, X10 : $i]: ~ (zip_tseitin_0 @ X7 @ X9 @ X10 @ X7)),
% 0.19/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.19/0.51  thf('20', plain, ($false), inference('sup-', [status(thm)], ['17', '19'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
