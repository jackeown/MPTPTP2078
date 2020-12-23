%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zUVO4Pdcq5

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:31 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   54 (  59 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  355 ( 413 expanded)
%              Number of equality atoms :   41 (  50 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('1',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('5',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('11',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
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

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X17 @ X21 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X14 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X18 @ X19 @ X20 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X18 @ X19 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zUVO4Pdcq5
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.67/0.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.87  % Solved by: fo/fo7.sh
% 0.67/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.87  % done 354 iterations in 0.427s
% 0.67/0.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.87  % SZS output start Refutation
% 0.67/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.87  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.67/0.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.67/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.67/0.87  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.67/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.87  thf(d1_enumset1, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.87     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.67/0.87       ( ![E:$i]:
% 0.67/0.87         ( ( r2_hidden @ E @ D ) <=>
% 0.67/0.87           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.67/0.87  thf(zf_stmt_0, axiom,
% 0.67/0.87    (![E:$i,C:$i,B:$i,A:$i]:
% 0.67/0.87     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.67/0.87       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.67/0.87  thf('0', plain,
% 0.67/0.87      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.67/0.87         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.67/0.87          | ((X13) = (X14))
% 0.67/0.87          | ((X13) = (X15))
% 0.67/0.87          | ((X13) = (X16)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(t18_zfmisc_1, conjecture,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.67/0.87         ( k1_tarski @ A ) ) =>
% 0.67/0.87       ( ( A ) = ( B ) ) ))).
% 0.67/0.87  thf(zf_stmt_1, negated_conjecture,
% 0.67/0.87    (~( ![A:$i,B:$i]:
% 0.67/0.87        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.67/0.87            ( k1_tarski @ A ) ) =>
% 0.67/0.87          ( ( A ) = ( B ) ) ) )),
% 0.67/0.87    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.67/0.87  thf('1', plain,
% 0.67/0.87      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.67/0.87         = (k1_tarski @ sk_A))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.67/0.87  thf(commutativity_k3_xboole_0, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.67/0.87  thf('2', plain,
% 0.67/0.87      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.67/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.67/0.87  thf('3', plain,
% 0.67/0.87      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.67/0.87         = (k1_tarski @ sk_A))),
% 0.67/0.87      inference('demod', [status(thm)], ['1', '2'])).
% 0.67/0.87  thf(t17_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.67/0.87  thf('4', plain,
% 0.67/0.87      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.67/0.87      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.67/0.87  thf('5', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.67/0.87      inference('sup+', [status(thm)], ['3', '4'])).
% 0.67/0.87  thf(t12_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.67/0.87  thf('6', plain,
% 0.67/0.87      (![X4 : $i, X5 : $i]:
% 0.67/0.87         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.67/0.87      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.67/0.87  thf('7', plain,
% 0.67/0.87      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.67/0.87         = (k1_tarski @ sk_B))),
% 0.67/0.87      inference('sup-', [status(thm)], ['5', '6'])).
% 0.67/0.87  thf(commutativity_k2_xboole_0, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.67/0.87  thf('8', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.87      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.67/0.87  thf('9', plain,
% 0.67/0.87      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.67/0.87         = (k1_tarski @ sk_B))),
% 0.67/0.87      inference('demod', [status(thm)], ['7', '8'])).
% 0.67/0.87  thf(t41_enumset1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( k2_tarski @ A @ B ) =
% 0.67/0.87       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.67/0.87  thf('10', plain,
% 0.67/0.87      (![X24 : $i, X25 : $i]:
% 0.67/0.87         ((k2_tarski @ X24 @ X25)
% 0.67/0.87           = (k2_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X25)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.67/0.87  thf('11', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.67/0.87      inference('demod', [status(thm)], ['9', '10'])).
% 0.67/0.87  thf(t70_enumset1, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.67/0.87  thf('12', plain,
% 0.67/0.87      (![X27 : $i, X28 : $i]:
% 0.67/0.87         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.67/0.87      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.67/0.87  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.67/0.87  thf(zf_stmt_3, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.87     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.67/0.87       ( ![E:$i]:
% 0.67/0.87         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.67/0.87  thf('13', plain,
% 0.67/0.87      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.67/0.87         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.67/0.87          | (r2_hidden @ X17 @ X21)
% 0.67/0.87          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.67/0.87  thf('14', plain,
% 0.67/0.87      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.67/0.87         ((r2_hidden @ X17 @ (k1_enumset1 @ X20 @ X19 @ X18))
% 0.67/0.87          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20))),
% 0.67/0.87      inference('simplify', [status(thm)], ['13'])).
% 0.67/0.87  thf('15', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.67/0.87          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.67/0.87      inference('sup+', [status(thm)], ['12', '14'])).
% 0.67/0.87  thf('16', plain,
% 0.67/0.87      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.67/0.87         (((X13) != (X14)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('17', plain,
% 0.67/0.87      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.67/0.87         ~ (zip_tseitin_0 @ X14 @ X14 @ X15 @ X12)),
% 0.67/0.87      inference('simplify', [status(thm)], ['16'])).
% 0.67/0.87  thf('18', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.67/0.87      inference('sup-', [status(thm)], ['15', '17'])).
% 0.67/0.87  thf('19', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.67/0.87      inference('sup+', [status(thm)], ['11', '18'])).
% 0.67/0.87  thf(t69_enumset1, axiom,
% 0.67/0.87    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.67/0.87  thf('20', plain,
% 0.67/0.87      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.67/0.87      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.67/0.87  thf('21', plain,
% 0.67/0.87      (![X27 : $i, X28 : $i]:
% 0.67/0.87         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.67/0.87      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.67/0.87  thf('22', plain,
% 0.67/0.87      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X22 @ X21)
% 0.67/0.87          | ~ (zip_tseitin_0 @ X22 @ X18 @ X19 @ X20)
% 0.67/0.87          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.67/0.87  thf('23', plain,
% 0.67/0.87      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i]:
% 0.67/0.87         (~ (zip_tseitin_0 @ X22 @ X18 @ X19 @ X20)
% 0.67/0.87          | ~ (r2_hidden @ X22 @ (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.67/0.87      inference('simplify', [status(thm)], ['22'])).
% 0.67/0.87  thf('24', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.67/0.87          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.67/0.87      inference('sup-', [status(thm)], ['21', '23'])).
% 0.67/0.87  thf('25', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.67/0.87          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['20', '24'])).
% 0.67/0.87  thf('26', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.67/0.87      inference('sup-', [status(thm)], ['19', '25'])).
% 0.67/0.87  thf('27', plain,
% 0.67/0.87      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['0', '26'])).
% 0.67/0.87  thf('28', plain, (((sk_A) = (sk_B))),
% 0.67/0.87      inference('simplify', [status(thm)], ['27'])).
% 0.67/0.87  thf('29', plain, (((sk_A) != (sk_B))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.67/0.87  thf('30', plain, ($false),
% 0.67/0.87      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.67/0.87  
% 0.67/0.87  % SZS output end Refutation
% 0.67/0.87  
% 0.71/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
