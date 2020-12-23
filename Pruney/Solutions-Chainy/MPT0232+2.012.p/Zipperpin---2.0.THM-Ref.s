%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GPRddVIAq7

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  48 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :  280 ( 304 expanded)
%              Number of equality atoms :   28 (  30 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t27_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( ( k2_tarski @ A @ B )
        = ( k1_tarski @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( ( k2_tarski @ A @ B )
          = ( k1_tarski @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33
        = ( k1_tarski @ X32 ) )
      | ( X33 = k1_xboole_0 )
      | ~ ( r1_tarski @ X33 @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('2',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
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

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','11'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['20'])).

thf('22',plain,(
    $false ),
    inference('sup-',[status(thm)],['12','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GPRddVIAq7
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 133 iterations in 0.082s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(t27_zfmisc_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.54       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.54        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.54          ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t27_zfmisc_1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(l3_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X32 : $i, X33 : $i]:
% 0.21/0.54         (((X33) = (k1_tarski @ X32))
% 0.21/0.54          | ((X33) = (k1_xboole_0))
% 0.21/0.54          | ~ (r1_tarski @ X33 @ (k1_tarski @ X32)))),
% 0.21/0.54      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.54        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('3', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('4', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf(t70_enumset1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X27 : $i, X28 : $i]:
% 0.21/0.54         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.21/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.54  thf(d1_enumset1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.54       ( ![E:$i]:
% 0.21/0.54         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.54           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_2, axiom,
% 0.21/0.54    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.54     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.54       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_3, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.54       ( ![E:$i]:
% 0.21/0.54         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.54         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 0.21/0.54          | (r2_hidden @ X19 @ X23)
% 0.21/0.54          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 0.21/0.54          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 0.21/0.54      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.54          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['5', '7'])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.54         (((X15) != (X14)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.21/0.54         ~ (zip_tseitin_0 @ X14 @ X16 @ X17 @ X14)),
% 0.21/0.54      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.54  thf('12', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.21/0.54      inference('sup+', [status(thm)], ['4', '11'])).
% 0.21/0.54  thf(t36_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.21/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.54  thf('14', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.54  thf(d10_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X6 : $i, X8 : $i]:
% 0.21/0.54         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.54  thf(d5_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.54       ( ![D:$i]:
% 0.21/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.54           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.54          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.54          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.54          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.54  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.54      inference('condensation', [status(thm)], ['20'])).
% 0.21/0.54  thf('22', plain, ($false), inference('sup-', [status(thm)], ['12', '21'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
