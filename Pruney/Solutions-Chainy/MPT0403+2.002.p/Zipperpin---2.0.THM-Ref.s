%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HYjuKpufEK

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:05 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  309 ( 348 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_setfam_1 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_setfam_1 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
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

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X15 )
      | ~ ( r2_hidden @ X10 @ X15 )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ( X12
       != ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X10: $i,X11: $i,X13: $i,X15: $i] :
      ( ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r2_hidden @ X10 @ X15 )
      | ( zip_tseitin_0 @ X11 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) @ X13 @ X15 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ X3 @ ( k2_xboole_0 @ X3 @ ( sk_C @ X1 @ X0 ) ) @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X3 @ X2 ) @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ X2 @ X0 )
      | ( r1_setfam_1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 @ X0 )
      | ( r1_setfam_1 @ X0 @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

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

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X18 @ X21 )
      | ( X21
       != ( k2_setfam_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k2_setfam_1 @ X20 @ X19 ) )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_setfam_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( r1_tarski @ ( sk_C @ X8 @ X7 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) )
      | ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HYjuKpufEK
% 0.15/0.37  % Computer   : n013.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 10:40:40 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.56  % Solved by: fo/fo7.sh
% 0.23/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.56  % done 84 iterations in 0.082s
% 0.23/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.56  % SZS output start Refutation
% 0.23/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.23/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.56  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.23/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.56  thf(k2_setfam_1_type, type, k2_setfam_1: $i > $i > $i).
% 0.23/0.56  thf(t29_setfam_1, conjecture,
% 0.23/0.56    (![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ))).
% 0.23/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.56    (~( ![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) )),
% 0.23/0.56    inference('cnf.neg', [status(esa)], [t29_setfam_1])).
% 0.23/0.56  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ (k2_setfam_1 @ sk_A @ sk_A))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(d10_xboole_0, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.56  thf('1', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.23/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.56  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.56      inference('simplify', [status(thm)], ['1'])).
% 0.23/0.56  thf(t12_xboole_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.23/0.56  thf('3', plain,
% 0.23/0.56      (![X3 : $i, X4 : $i]:
% 0.23/0.56         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.23/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.23/0.56  thf('4', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.56  thf(d2_setfam_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.23/0.56       ( ![C:$i]:
% 0.23/0.56         ( ~( ( r2_hidden @ C @ A ) & 
% 0.23/0.56              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.23/0.56  thf('5', plain,
% 0.23/0.56      (![X7 : $i, X8 : $i]:
% 0.23/0.56         ((r1_setfam_1 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 0.23/0.56      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.23/0.56  thf('6', plain,
% 0.23/0.56      (![X7 : $i, X8 : $i]:
% 0.23/0.56         ((r1_setfam_1 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 0.23/0.56      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.23/0.56  thf(d4_setfam_1, axiom,
% 0.23/0.56    (![A:$i,B:$i,C:$i]:
% 0.23/0.56     ( ( ( C ) = ( k2_setfam_1 @ A @ B ) ) <=>
% 0.23/0.56       ( ![D:$i]:
% 0.23/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.23/0.56           ( ?[E:$i,F:$i]:
% 0.23/0.56             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.23/0.56               ( ( D ) = ( k2_xboole_0 @ E @ F ) ) ) ) ) ) ))).
% 0.23/0.56  thf(zf_stmt_1, axiom,
% 0.23/0.56    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.23/0.56     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.23/0.56       ( ( ( D ) = ( k2_xboole_0 @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.23/0.56         ( r2_hidden @ E @ A ) ) ))).
% 0.23/0.56  thf('7', plain,
% 0.23/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 0.23/0.56         ((zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X15)
% 0.23/0.56          | ~ (r2_hidden @ X10 @ X15)
% 0.23/0.56          | ~ (r2_hidden @ X11 @ X13)
% 0.23/0.56          | ((X12) != (k2_xboole_0 @ X10 @ X11)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.23/0.56  thf('8', plain,
% 0.23/0.56      (![X10 : $i, X11 : $i, X13 : $i, X15 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X11 @ X13)
% 0.23/0.56          | ~ (r2_hidden @ X10 @ X15)
% 0.23/0.56          | (zip_tseitin_0 @ X11 @ X10 @ (k2_xboole_0 @ X10 @ X11) @ X13 @ X15))),
% 0.23/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.23/0.56  thf('9', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.56         ((r1_setfam_1 @ X0 @ X1)
% 0.23/0.56          | (zip_tseitin_0 @ (sk_C @ X1 @ X0) @ X3 @ 
% 0.23/0.56             (k2_xboole_0 @ X3 @ (sk_C @ X1 @ X0)) @ X0 @ X2)
% 0.23/0.56          | ~ (r2_hidden @ X3 @ X2))),
% 0.23/0.56      inference('sup-', [status(thm)], ['6', '8'])).
% 0.23/0.56  thf('10', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.56         ((r1_setfam_1 @ X0 @ X1)
% 0.23/0.56          | (zip_tseitin_0 @ (sk_C @ X3 @ X2) @ (sk_C @ X1 @ X0) @ 
% 0.23/0.56             (k2_xboole_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ X2 @ X0)
% 0.23/0.56          | (r1_setfam_1 @ X2 @ X3))),
% 0.23/0.56      inference('sup-', [status(thm)], ['5', '9'])).
% 0.23/0.56  thf('11', plain,
% 0.23/0.57      (![X0 : $i, X1 : $i]:
% 0.23/0.57         ((zip_tseitin_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X1 @ X0) @ 
% 0.23/0.57           (sk_C @ X1 @ X0) @ X0 @ X0)
% 0.23/0.57          | (r1_setfam_1 @ X0 @ X1)
% 0.23/0.57          | (r1_setfam_1 @ X0 @ X1))),
% 0.23/0.57      inference('sup+', [status(thm)], ['4', '10'])).
% 0.23/0.57  thf('12', plain,
% 0.23/0.57      (![X0 : $i, X1 : $i]:
% 0.23/0.57         ((r1_setfam_1 @ X0 @ X1)
% 0.23/0.57          | (zip_tseitin_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X1 @ X0) @ 
% 0.23/0.57             (sk_C @ X1 @ X0) @ X0 @ X0))),
% 0.23/0.57      inference('simplify', [status(thm)], ['11'])).
% 0.23/0.57  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.23/0.57  thf(zf_stmt_3, axiom,
% 0.23/0.57    (![A:$i,B:$i,C:$i]:
% 0.23/0.57     ( ( ( C ) = ( k2_setfam_1 @ A @ B ) ) <=>
% 0.23/0.57       ( ![D:$i]:
% 0.23/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.23/0.57           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.23/0.57  thf('13', plain,
% 0.23/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.23/0.57         (~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.23/0.57          | (r2_hidden @ X18 @ X21)
% 0.23/0.57          | ((X21) != (k2_setfam_1 @ X20 @ X19)))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.23/0.57  thf('14', plain,
% 0.23/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.23/0.57         ((r2_hidden @ X18 @ (k2_setfam_1 @ X20 @ X19))
% 0.23/0.57          | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.23/0.57      inference('simplify', [status(thm)], ['13'])).
% 0.23/0.57  thf('15', plain,
% 0.23/0.57      (![X0 : $i, X1 : $i]:
% 0.23/0.57         ((r1_setfam_1 @ X0 @ X1)
% 0.23/0.57          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['12', '14'])).
% 0.23/0.57  thf('16', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.57      inference('simplify', [status(thm)], ['1'])).
% 0.23/0.57  thf('17', plain,
% 0.23/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.57         ((r1_setfam_1 @ X7 @ X8)
% 0.23/0.57          | ~ (r2_hidden @ X9 @ X8)
% 0.23/0.57          | ~ (r1_tarski @ (sk_C @ X8 @ X7) @ X9))),
% 0.23/0.57      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.23/0.57  thf('18', plain,
% 0.23/0.57      (![X0 : $i, X1 : $i]:
% 0.23/0.57         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ X1) | (r1_setfam_1 @ X0 @ X1))),
% 0.23/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.57  thf('19', plain,
% 0.23/0.57      (![X0 : $i]:
% 0.23/0.57         ((r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0))
% 0.23/0.57          | (r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['15', '18'])).
% 0.23/0.57  thf('20', plain, (![X0 : $i]: (r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0))),
% 0.23/0.57      inference('simplify', [status(thm)], ['19'])).
% 0.23/0.57  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 0.23/0.57  
% 0.23/0.57  % SZS output end Refutation
% 0.23/0.57  
% 0.23/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
