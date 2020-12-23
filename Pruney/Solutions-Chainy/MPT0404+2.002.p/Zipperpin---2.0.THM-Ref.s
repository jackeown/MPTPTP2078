%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UCPOOjcF7Q

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  43 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  334 ( 434 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_setfam_1_type,type,(
    k3_setfam_1: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t30_setfam_1,conjecture,(
    ! [A: $i] :
      ( r1_setfam_1 @ ( k3_setfam_1 @ A @ A ) @ A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_setfam_1 @ ( k3_setfam_1 @ A @ A ) @ A ) ),
    inference('cnf.neg',[status(esa)],[t30_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ ( k3_setfam_1 @ sk_A @ sk_A ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_setfam_1 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf(d5_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_setfam_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k3_xboole_0 @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k3_xboole_0 @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_setfam_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X21 @ X18 @ X19 ) @ ( sk_E_1 @ X21 @ X18 @ X19 ) @ X21 @ X18 @ X19 )
      | ( X20
       != ( k3_setfam_1 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X21 @ X18 @ X19 ) @ ( sk_E_1 @ X21 @ X18 @ X19 ) @ X21 @ X18 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k3_setfam_1 @ X19 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k3_setfam_1 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X9 @ X13 )
      | ~ ( zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k3_setfam_1 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k3_setfam_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ ( sk_F_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) )
      | ( r1_setfam_1 @ ( k3_setfam_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_setfam_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r1_tarski @ ( sk_C @ X7 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X2 )
      | ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k3_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X2 )
      | ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X0 )
      | ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_setfam_1 @ ( k3_setfam_1 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['0','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UCPOOjcF7Q
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:15:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 51 iterations in 0.053s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(k3_setfam_1_type, type, k3_setfam_1: $i > $i > $i).
% 0.19/0.50  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.50  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.19/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(t30_setfam_1, conjecture,
% 0.19/0.50    (![A:$i]: ( r1_setfam_1 @ ( k3_setfam_1 @ A @ A ) @ A ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]: ( r1_setfam_1 @ ( k3_setfam_1 @ A @ A ) @ A ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t30_setfam_1])).
% 0.19/0.50  thf('0', plain, (~ (r1_setfam_1 @ (k3_setfam_1 @ sk_A @ sk_A) @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d2_setfam_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.19/0.50       ( ![C:$i]:
% 0.19/0.50         ( ~( ( r2_hidden @ C @ A ) & 
% 0.19/0.50              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i]:
% 0.19/0.50         ((r1_setfam_1 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.19/0.50  thf(d5_setfam_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( ( C ) = ( k3_setfam_1 @ A @ B ) ) <=>
% 0.19/0.50       ( ![D:$i]:
% 0.19/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.50           ( ?[E:$i,F:$i]:
% 0.19/0.50             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.19/0.50               ( ( D ) = ( k3_xboole_0 @ E @ F ) ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.19/0.50  thf(zf_stmt_2, axiom,
% 0.19/0.50    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.19/0.50     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.19/0.50       ( ( ( D ) = ( k3_xboole_0 @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.19/0.50         ( r2_hidden @ E @ A ) ) ))).
% 0.19/0.50  thf(zf_stmt_3, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( ( C ) = ( k3_setfam_1 @ A @ B ) ) <=>
% 0.19/0.50       ( ![D:$i]:
% 0.19/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.50           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X21 @ X20)
% 0.19/0.50          | (zip_tseitin_0 @ (sk_F_1 @ X21 @ X18 @ X19) @ 
% 0.19/0.50             (sk_E_1 @ X21 @ X18 @ X19) @ X21 @ X18 @ X19)
% 0.19/0.50          | ((X20) != (k3_setfam_1 @ X19 @ X18)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.19/0.50         ((zip_tseitin_0 @ (sk_F_1 @ X21 @ X18 @ X19) @ 
% 0.19/0.50           (sk_E_1 @ X21 @ X18 @ X19) @ X21 @ X18 @ X19)
% 0.19/0.50          | ~ (r2_hidden @ X21 @ (k3_setfam_1 @ X19 @ X18)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_setfam_1 @ (k3_setfam_1 @ X1 @ X0) @ X2)
% 0.19/0.50          | (zip_tseitin_0 @ 
% 0.19/0.50             (sk_F_1 @ (sk_C @ X2 @ (k3_setfam_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.19/0.50             (sk_E_1 @ (sk_C @ X2 @ (k3_setfam_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.19/0.50             (sk_C @ X2 @ (k3_setfam_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '3'])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.50         ((r2_hidden @ X9 @ X13)
% 0.19/0.50          | ~ (zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_setfam_1 @ (k3_setfam_1 @ X0 @ X1) @ X2)
% 0.19/0.50          | (r2_hidden @ 
% 0.19/0.50             (sk_E_1 @ (sk_C @ X2 @ (k3_setfam_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_setfam_1 @ (k3_setfam_1 @ X1 @ X0) @ X2)
% 0.19/0.50          | (zip_tseitin_0 @ 
% 0.19/0.50             (sk_F_1 @ (sk_C @ X2 @ (k3_setfam_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.19/0.50             (sk_E_1 @ (sk_C @ X2 @ (k3_setfam_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.19/0.50             (sk_C @ X2 @ (k3_setfam_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '3'])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.50         (((X11) = (k3_xboole_0 @ X9 @ X10))
% 0.19/0.50          | ~ (zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_setfam_1 @ (k3_setfam_1 @ X0 @ X1) @ X2)
% 0.19/0.50          | ((sk_C @ X2 @ (k3_setfam_1 @ X0 @ X1))
% 0.19/0.50              = (k3_xboole_0 @ 
% 0.19/0.50                 (sk_E_1 @ (sk_C @ X2 @ (k3_setfam_1 @ X0 @ X1)) @ X1 @ X0) @ 
% 0.19/0.50                 (sk_F_1 @ (sk_C @ X2 @ (k3_setfam_1 @ X0 @ X1)) @ X1 @ X0))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.50  thf(t17_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.19/0.50      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_tarski @ (sk_C @ X2 @ (k3_setfam_1 @ X1 @ X0)) @ 
% 0.19/0.50           (sk_E_1 @ (sk_C @ X2 @ (k3_setfam_1 @ X1 @ X0)) @ X0 @ X1))
% 0.19/0.50          | (r1_setfam_1 @ (k3_setfam_1 @ X1 @ X0) @ X2))),
% 0.19/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.50         ((r1_setfam_1 @ X6 @ X7)
% 0.19/0.50          | ~ (r2_hidden @ X8 @ X7)
% 0.19/0.50          | ~ (r1_tarski @ (sk_C @ X7 @ X6) @ X8))),
% 0.19/0.50      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_setfam_1 @ (k3_setfam_1 @ X0 @ X1) @ X2)
% 0.19/0.50          | ~ (r2_hidden @ 
% 0.19/0.50               (sk_E_1 @ (sk_C @ X2 @ (k3_setfam_1 @ X0 @ X1)) @ X1 @ X0) @ X2)
% 0.19/0.50          | (r1_setfam_1 @ (k3_setfam_1 @ X0 @ X1) @ X2))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (r2_hidden @ 
% 0.19/0.50             (sk_E_1 @ (sk_C @ X2 @ (k3_setfam_1 @ X0 @ X1)) @ X1 @ X0) @ X2)
% 0.19/0.50          | (r1_setfam_1 @ (k3_setfam_1 @ X0 @ X1) @ X2))),
% 0.19/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((r1_setfam_1 @ (k3_setfam_1 @ X0 @ X1) @ X0)
% 0.19/0.50          | (r1_setfam_1 @ (k3_setfam_1 @ X0 @ X1) @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '14'])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: (r1_setfam_1 @ (k3_setfam_1 @ X0 @ X1) @ X0)),
% 0.19/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.50  thf('17', plain, ($false), inference('demod', [status(thm)], ['0', '16'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
