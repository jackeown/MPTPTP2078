%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XyxhxF9X7T

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  67 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  390 ( 651 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_setfam_1_type,type,(
    k2_setfam_1: $i > $i > $i )).

thf(t29_setfam_1,conjecture,(
    ! [A: $i] :
      ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t29_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ sk_A @ ( k2_setfam_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_setfam_1 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_setfam_1 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf(d4_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_setfam_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k2_xboole_0 @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k2_xboole_0 @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X11 )
      | ~ ( r2_hidden @ X6 @ X11 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ( X8
       != ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X6 @ X11 )
      | ( zip_tseitin_0 @ X7 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) @ X9 @ X11 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ X3 @ ( k2_xboole_0 @ X3 @ ( sk_C @ X1 @ X0 ) ) @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X3 @ X2 ) @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ X2 @ X0 )
      | ( r1_setfam_1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 @ X0 )
      | ( r1_setfam_1 @ X0 @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_setfam_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X14 @ X17 )
      | ( X17
       != ( k2_setfam_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k2_setfam_1 @ X16 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(reflexivity_r1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_setfam_1 @ A @ A ) )).

thf('13',plain,(
    ! [X22: $i] :
      ( r1_setfam_1 @ X22 @ X22 ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_setfam_1])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X2 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r1_setfam_1 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X22: $i] :
      ( r1_setfam_1 @ X22 @ X22 ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ ( sk_D @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r1_setfam_1 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ~ ( r1_setfam_1 @ ( k2_setfam_1 @ X0 @ X0 ) @ X2 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_setfam_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( r1_tarski @ ( sk_C @ X4 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) )
      | ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XyxhxF9X7T
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:43:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 58 iterations in 0.060s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k2_setfam_1_type, type, k2_setfam_1: $i > $i > $i).
% 0.20/0.50  thf(t29_setfam_1, conjecture,
% 0.20/0.50    (![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t29_setfam_1])).
% 0.20/0.50  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ (k2_setfam_1 @ sk_A @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.50  thf('1', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.50  thf(d2_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.50              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.50  thf(d4_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( C ) = ( k2_setfam_1 @ A @ B ) ) <=>
% 0.20/0.50       ( ![D:$i]:
% 0.20/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.50           ( ?[E:$i,F:$i]:
% 0.20/0.50             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.50               ( ( D ) = ( k2_xboole_0 @ E @ F ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_1, axiom,
% 0.20/0.50    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.20/0.50       ( ( ( D ) = ( k2_xboole_0 @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.50         ( r2_hidden @ E @ A ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.20/0.50         ((zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X11)
% 0.20/0.50          | ~ (r2_hidden @ X6 @ X11)
% 0.20/0.50          | ~ (r2_hidden @ X7 @ X9)
% 0.20/0.50          | ((X8) != (k2_xboole_0 @ X6 @ X7)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X9 : $i, X11 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X7 @ X9)
% 0.20/0.50          | ~ (r2_hidden @ X6 @ X11)
% 0.20/0.50          | (zip_tseitin_0 @ X7 @ X6 @ (k2_xboole_0 @ X6 @ X7) @ X9 @ X11))),
% 0.20/0.50      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.50          | (zip_tseitin_0 @ (sk_C @ X1 @ X0) @ X3 @ 
% 0.20/0.50             (k2_xboole_0 @ X3 @ (sk_C @ X1 @ X0)) @ X0 @ X2)
% 0.20/0.50          | ~ (r2_hidden @ X3 @ X2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.50          | (zip_tseitin_0 @ (sk_C @ X3 @ X2) @ (sk_C @ X1 @ X0) @ 
% 0.20/0.50             (k2_xboole_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ X2 @ X0)
% 0.20/0.50          | (r1_setfam_1 @ X2 @ X3))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((zip_tseitin_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X1 @ X0) @ 
% 0.20/0.50           (sk_C @ X1 @ X0) @ X0 @ X0)
% 0.20/0.50          | (r1_setfam_1 @ X0 @ X1)
% 0.20/0.50          | (r1_setfam_1 @ X0 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.50          | (zip_tseitin_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X1 @ X0) @ 
% 0.20/0.50             (sk_C @ X1 @ X0) @ X0 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.50  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_3, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( C ) = ( k2_setfam_1 @ A @ B ) ) <=>
% 0.20/0.50       ( ![D:$i]:
% 0.20/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.50           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.20/0.50          | (r2_hidden @ X14 @ X17)
% 0.20/0.50          | ((X17) != (k2_setfam_1 @ X16 @ X15)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.50         ((r2_hidden @ X14 @ (k2_setfam_1 @ X16 @ X15))
% 0.20/0.50          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16))),
% 0.20/0.50      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.50  thf(reflexivity_r1_setfam_1, axiom, (![A:$i,B:$i]: ( r1_setfam_1 @ A @ A ))).
% 0.20/0.50  thf('13', plain, (![X22 : $i]: (r1_setfam_1 @ X22 @ X22)),
% 0.20/0.50      inference('cnf', [status(esa)], [reflexivity_r1_setfam_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_D @ X1 @ X2) @ X2)
% 0.20/0.50          | ~ (r2_hidden @ X1 @ X3)
% 0.20/0.50          | ~ (r1_setfam_1 @ X3 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X1 @ X0) | (r2_hidden @ (sk_D @ X1 @ X0) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ (sk_D @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)) @ 
% 0.20/0.50             (k2_setfam_1 @ X0 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '15'])).
% 0.20/0.50  thf('17', plain, (![X22 : $i]: (r1_setfam_1 @ X22 @ X22)),
% 0.20/0.50      inference('cnf', [status(esa)], [reflexivity_r1_setfam_1])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ (sk_D @ X1 @ X2))
% 0.20/0.50          | ~ (r2_hidden @ X1 @ X3)
% 0.20/0.50          | ~ (r1_setfam_1 @ X3 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.50          | ~ (r1_setfam_1 @ (k2_setfam_1 @ X0 @ X0) @ X2)
% 0.20/0.50          | (r1_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ (sk_C @ X1 @ X0) @ X2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ (sk_C @ X1 @ X0) @ 
% 0.20/0.50           (sk_D @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)))
% 0.20/0.50          | (r1_setfam_1 @ X0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X3 @ X4)
% 0.20/0.50          | ~ (r2_hidden @ X5 @ X4)
% 0.20/0.50          | ~ (r1_tarski @ (sk_C @ X4 @ X3) @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.50          | ~ (r2_hidden @ 
% 0.20/0.50               (sk_D @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)) @ X1)
% 0.20/0.50          | (r1_setfam_1 @ X0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ (sk_D @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)) @ 
% 0.20/0.50             X1)
% 0.20/0.50          | (r1_setfam_1 @ X0 @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0))
% 0.20/0.50          | (r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '24'])).
% 0.20/0.50  thf('26', plain, (![X0 : $i]: (r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.50  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
