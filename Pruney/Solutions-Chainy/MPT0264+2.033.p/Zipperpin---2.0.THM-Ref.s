%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LOCDO1uJIU

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:42 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   44 (  51 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  311 ( 403 expanded)
%              Number of equality atoms :   31 (  44 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
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

thf('1',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
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

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k3_xboole_0 @ ( k2_tarski @ X0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LOCDO1uJIU
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:39:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.52/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.72  % Solved by: fo/fo7.sh
% 0.52/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.72  % done 259 iterations in 0.219s
% 0.52/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.72  % SZS output start Refutation
% 0.52/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.52/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.72  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.52/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.72  thf(d1_enumset1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.72     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.52/0.72       ( ![E:$i]:
% 0.52/0.72         ( ( r2_hidden @ E @ D ) <=>
% 0.52/0.72           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_0, axiom,
% 0.52/0.72    (![E:$i,C:$i,B:$i,A:$i]:
% 0.52/0.72     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.52/0.72       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.52/0.72  thf('0', plain,
% 0.52/0.72      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.72         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.52/0.72          | ((X9) = (X10))
% 0.52/0.72          | ((X9) = (X11))
% 0.52/0.72          | ((X9) = (X12)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(t59_zfmisc_1, conjecture,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.52/0.72          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_1, negated_conjecture,
% 0.52/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.72        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.52/0.72             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 0.52/0.72    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 0.52/0.72  thf('1', plain,
% 0.52/0.72      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.72  thf(t70_enumset1, axiom,
% 0.52/0.72    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.52/0.72  thf('2', plain,
% 0.52/0.72      (![X21 : $i, X22 : $i]:
% 0.52/0.72         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.52/0.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.72  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.52/0.72  thf(zf_stmt_3, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.72     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.52/0.72       ( ![E:$i]:
% 0.52/0.72         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.52/0.72  thf('3', plain,
% 0.52/0.72      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.72         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.52/0.72          | (r2_hidden @ X13 @ X17)
% 0.52/0.72          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.72  thf('4', plain,
% 0.52/0.72      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.52/0.72         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.52/0.72          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.52/0.72      inference('simplify', [status(thm)], ['3'])).
% 0.52/0.72  thf('5', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.72         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.52/0.72          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.52/0.72      inference('sup+', [status(thm)], ['2', '4'])).
% 0.52/0.72  thf('6', plain,
% 0.52/0.72      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.52/0.72         (((X9) != (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('7', plain,
% 0.52/0.72      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X10 @ X10 @ X11 @ X8)),
% 0.52/0.72      inference('simplify', [status(thm)], ['6'])).
% 0.52/0.72  thf('8', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['5', '7'])).
% 0.52/0.72  thf('9', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.72  thf(d4_xboole_0, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.52/0.72       ( ![D:$i]:
% 0.52/0.72         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.72           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.52/0.72  thf('10', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X0 @ X1)
% 0.52/0.72          | ~ (r2_hidden @ X0 @ X2)
% 0.52/0.72          | (r2_hidden @ X0 @ X3)
% 0.52/0.72          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.52/0.72  thf('11', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.72         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.52/0.72          | ~ (r2_hidden @ X0 @ X2)
% 0.52/0.72          | ~ (r2_hidden @ X0 @ X1))),
% 0.52/0.72      inference('simplify', [status(thm)], ['10'])).
% 0.52/0.72  thf('12', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (r2_hidden @ sk_B @ X0)
% 0.52/0.72          | (r2_hidden @ sk_B @ (k3_xboole_0 @ X0 @ sk_C)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['9', '11'])).
% 0.52/0.72  thf('13', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (r2_hidden @ sk_B @ (k3_xboole_0 @ (k2_tarski @ X0 @ sk_B) @ sk_C))),
% 0.52/0.72      inference('sup-', [status(thm)], ['8', '12'])).
% 0.52/0.72  thf('14', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.52/0.72      inference('sup+', [status(thm)], ['1', '13'])).
% 0.52/0.72  thf(t69_enumset1, axiom,
% 0.52/0.72    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.52/0.72  thf('15', plain,
% 0.52/0.72      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.52/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.72  thf('16', plain,
% 0.52/0.72      (![X21 : $i, X22 : $i]:
% 0.52/0.72         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.52/0.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.72  thf('17', plain,
% 0.52/0.72      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X18 @ X17)
% 0.52/0.72          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.52/0.72          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.72  thf('18', plain,
% 0.52/0.72      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.52/0.72         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.52/0.72          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.52/0.72      inference('simplify', [status(thm)], ['17'])).
% 0.52/0.72  thf('19', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.52/0.72          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['16', '18'])).
% 0.52/0.72  thf('20', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.52/0.72          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['15', '19'])).
% 0.52/0.72  thf('21', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 0.52/0.72      inference('sup-', [status(thm)], ['14', '20'])).
% 0.52/0.72  thf('22', plain,
% 0.52/0.72      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['0', '21'])).
% 0.52/0.72  thf('23', plain, (((sk_B) = (sk_A))),
% 0.52/0.72      inference('simplify', [status(thm)], ['22'])).
% 0.52/0.72  thf('24', plain, (((sk_A) != (sk_B))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.72  thf('25', plain, ($false),
% 0.52/0.72      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.52/0.72  
% 0.52/0.72  % SZS output end Refutation
% 0.52/0.72  
% 0.52/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
