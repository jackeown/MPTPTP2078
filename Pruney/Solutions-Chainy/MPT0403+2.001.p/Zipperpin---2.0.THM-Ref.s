%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ClsYpBS6I1

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  39 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  295 ( 319 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X6: $i,X7: $i] :
      ( ( r1_setfam_1 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_setfam_1 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X14 )
      | ~ ( r2_hidden @ X9 @ X14 )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ( X11
       != ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X9: $i,X10: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X9 @ X14 )
      | ( zip_tseitin_0 @ X10 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) @ X12 @ X14 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X17 @ X20 )
      | ( X20
       != ( k2_setfam_1 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X17 @ ( k2_setfam_1 @ X19 @ X18 ) )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_setfam_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r1_tarski @ ( sk_C @ X7 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) )
      | ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ClsYpBS6I1
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 72 iterations in 0.113s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.57  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(k2_setfam_1_type, type, k2_setfam_1: $i > $i > $i).
% 0.20/0.57  thf(t29_setfam_1, conjecture,
% 0.20/0.57    (![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t29_setfam_1])).
% 0.20/0.57  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ (k2_setfam_1 @ sk_A @ sk_A))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.57  thf('1', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.57      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.57  thf(d2_setfam_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.20/0.57       ( ![C:$i]:
% 0.20/0.57         ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.57              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i]:
% 0.20/0.57         ((r1_setfam_1 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i]:
% 0.20/0.57         ((r1_setfam_1 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.57  thf(d4_setfam_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( C ) = ( k2_setfam_1 @ A @ B ) ) <=>
% 0.20/0.57       ( ![D:$i]:
% 0.20/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.57           ( ?[E:$i,F:$i]:
% 0.20/0.57             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.57               ( ( D ) = ( k2_xboole_0 @ E @ F ) ) ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_1, axiom,
% 0.20/0.57    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.20/0.57     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.20/0.57       ( ( ( D ) = ( k2_xboole_0 @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.57         ( r2_hidden @ E @ A ) ) ))).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.20/0.57         ((zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X14)
% 0.20/0.57          | ~ (r2_hidden @ X9 @ X14)
% 0.20/0.57          | ~ (r2_hidden @ X10 @ X12)
% 0.20/0.57          | ((X11) != (k2_xboole_0 @ X9 @ X10)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i, X12 : $i, X14 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X10 @ X12)
% 0.20/0.57          | ~ (r2_hidden @ X9 @ X14)
% 0.20/0.57          | (zip_tseitin_0 @ X10 @ X9 @ (k2_xboole_0 @ X9 @ X10) @ X12 @ X14))),
% 0.20/0.57      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.57         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.57          | (zip_tseitin_0 @ (sk_C @ X1 @ X0) @ X3 @ 
% 0.20/0.57             (k2_xboole_0 @ X3 @ (sk_C @ X1 @ X0)) @ X0 @ X2)
% 0.20/0.57          | ~ (r2_hidden @ X3 @ X2))),
% 0.20/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.57         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.57          | (zip_tseitin_0 @ (sk_C @ X3 @ X2) @ (sk_C @ X1 @ X0) @ 
% 0.20/0.57             (k2_xboole_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ X2 @ X0)
% 0.20/0.57          | (r1_setfam_1 @ X2 @ X3))),
% 0.20/0.57      inference('sup-', [status(thm)], ['2', '6'])).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((zip_tseitin_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X1 @ X0) @ 
% 0.20/0.57           (sk_C @ X1 @ X0) @ X0 @ X0)
% 0.20/0.57          | (r1_setfam_1 @ X0 @ X1)
% 0.20/0.57          | (r1_setfam_1 @ X0 @ X1))),
% 0.20/0.57      inference('sup+', [status(thm)], ['1', '7'])).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.57          | (zip_tseitin_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X1 @ X0) @ 
% 0.20/0.57             (sk_C @ X1 @ X0) @ X0 @ X0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.57  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.57  thf(zf_stmt_3, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( C ) = ( k2_setfam_1 @ A @ B ) ) <=>
% 0.20/0.57       ( ![D:$i]:
% 0.20/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.57           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.57         (~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.20/0.57          | (r2_hidden @ X17 @ X20)
% 0.20/0.57          | ((X20) != (k2_setfam_1 @ X19 @ X18)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.57         ((r2_hidden @ X17 @ (k2_setfam_1 @ X19 @ X18))
% 0.20/0.57          | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19))),
% 0.20/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((r1_setfam_1 @ X0 @ X1)
% 0.20/0.57          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.57  thf(d10_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.57  thf('14', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.20/0.57      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.57         ((r1_setfam_1 @ X6 @ X7)
% 0.20/0.57          | ~ (r2_hidden @ X8 @ X7)
% 0.20/0.57          | ~ (r1_tarski @ (sk_C @ X7 @ X6) @ X8))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ X1) | (r1_setfam_1 @ X0 @ X1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0))
% 0.20/0.57          | (r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['12', '16'])).
% 0.20/0.57  thf('18', plain, (![X0 : $i]: (r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.57  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
