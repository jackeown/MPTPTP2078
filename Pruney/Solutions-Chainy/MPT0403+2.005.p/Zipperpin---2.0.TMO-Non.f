%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ow36ql37ZJ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:05 EST 2020

% Result     : Timeout 57.95s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   54 (  90 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :   16
%              Number of atoms          :  505 (1017 expanded)
%              Number of equality atoms :   16 (  38 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

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

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('4',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('8',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_setfam_1 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_setfam_1 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
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

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X16 )
      | ~ ( r2_hidden @ X11 @ X16 )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ( X13
       != ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    ! [X11: $i,X12: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X11 @ X16 )
      | ( zip_tseitin_0 @ X12 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) @ X14 @ X16 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ X3 @ ( k2_xboole_0 @ X3 @ ( sk_C @ X1 @ X0 ) ) @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X3 @ X2 ) @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ X2 @ X0 )
      | ( r1_setfam_1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 @ X0 )
      | ( r1_setfam_1 @ X0 @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

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

thf('17',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X19 @ X22 )
      | ( X22
       != ( k2_setfam_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X19 @ ( k2_setfam_1 @ X21 @ X20 ) )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf(reflexivity_r1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_setfam_1 @ A @ A ) )).

thf('20',plain,(
    ! [X27: $i] :
      ( r1_setfam_1 @ X27 @ X27 ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_setfam_1])).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X6 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r1_setfam_1 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X27: $i] :
      ( r1_setfam_1 @ X27 @ X27 ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_setfam_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ ( sk_D_1 @ X6 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r1_setfam_1 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ~ ( r1_setfam_1 @ ( k2_setfam_1 @ X0 @ X0 ) @ X2 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_setfam_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r1_tarski @ ( sk_C @ X9 @ X8 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) )
      | ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ow36ql37ZJ
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 57.95/58.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 57.95/58.18  % Solved by: fo/fo7.sh
% 57.95/58.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 57.95/58.18  % done 19418 iterations in 57.720s
% 57.95/58.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 57.95/58.18  % SZS output start Refutation
% 57.95/58.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 57.95/58.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 57.95/58.18  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 57.95/58.18  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 57.95/58.18  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 57.95/58.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 57.95/58.18  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 57.95/58.18  thf(sk_A_type, type, sk_A: $i).
% 57.95/58.18  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 57.95/58.18  thf(k2_setfam_1_type, type, k2_setfam_1: $i > $i > $i).
% 57.95/58.18  thf(t29_setfam_1, conjecture,
% 57.95/58.18    (![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ))).
% 57.95/58.18  thf(zf_stmt_0, negated_conjecture,
% 57.95/58.18    (~( ![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) )),
% 57.95/58.18    inference('cnf.neg', [status(esa)], [t29_setfam_1])).
% 57.95/58.18  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ (k2_setfam_1 @ sk_A @ sk_A))),
% 57.95/58.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.95/58.18  thf(d3_xboole_0, axiom,
% 57.95/58.18    (![A:$i,B:$i,C:$i]:
% 57.95/58.18     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 57.95/58.18       ( ![D:$i]:
% 57.95/58.18         ( ( r2_hidden @ D @ C ) <=>
% 57.95/58.18           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 57.95/58.18  thf('1', plain,
% 57.95/58.18      (![X1 : $i, X3 : $i, X5 : $i]:
% 57.95/58.18         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 57.95/58.18          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 57.95/58.18          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 57.95/58.18          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 57.95/58.18      inference('cnf', [status(esa)], [d3_xboole_0])).
% 57.95/58.18  thf('2', plain,
% 57.95/58.18      (![X0 : $i, X1 : $i]:
% 57.95/58.18         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 57.95/58.18          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 57.95/58.18          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 57.95/58.18      inference('eq_fact', [status(thm)], ['1'])).
% 57.95/58.18  thf('3', plain,
% 57.95/58.18      (![X0 : $i]:
% 57.95/58.18         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 57.95/58.18          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 57.95/58.18      inference('eq_fact', [status(thm)], ['2'])).
% 57.95/58.18  thf('4', plain,
% 57.95/58.18      (![X1 : $i, X3 : $i, X5 : $i]:
% 57.95/58.18         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 57.95/58.18          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 57.95/58.18          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 57.95/58.18      inference('cnf', [status(esa)], [d3_xboole_0])).
% 57.95/58.18  thf('5', plain,
% 57.95/58.18      (![X0 : $i]:
% 57.95/58.18         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 57.95/58.18          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 57.95/58.18          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 57.95/58.18      inference('sup-', [status(thm)], ['3', '4'])).
% 57.95/58.18  thf('6', plain,
% 57.95/58.18      (![X0 : $i]:
% 57.95/58.18         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 57.95/58.18          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 57.95/58.18      inference('simplify', [status(thm)], ['5'])).
% 57.95/58.18  thf('7', plain,
% 57.95/58.18      (![X0 : $i]:
% 57.95/58.18         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 57.95/58.18          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 57.95/58.18      inference('eq_fact', [status(thm)], ['2'])).
% 57.95/58.18  thf('8', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 57.95/58.18      inference('clc', [status(thm)], ['6', '7'])).
% 57.95/58.18  thf(d2_setfam_1, axiom,
% 57.95/58.18    (![A:$i,B:$i]:
% 57.95/58.18     ( ( r1_setfam_1 @ A @ B ) <=>
% 57.95/58.18       ( ![C:$i]:
% 57.95/58.18         ( ~( ( r2_hidden @ C @ A ) & 
% 57.95/58.18              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 57.95/58.18  thf('9', plain,
% 57.95/58.18      (![X8 : $i, X9 : $i]:
% 57.95/58.18         ((r1_setfam_1 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 57.95/58.18      inference('cnf', [status(esa)], [d2_setfam_1])).
% 57.95/58.18  thf('10', plain,
% 57.95/58.18      (![X8 : $i, X9 : $i]:
% 57.95/58.18         ((r1_setfam_1 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 57.95/58.18      inference('cnf', [status(esa)], [d2_setfam_1])).
% 57.95/58.18  thf(d4_setfam_1, axiom,
% 57.95/58.18    (![A:$i,B:$i,C:$i]:
% 57.95/58.18     ( ( ( C ) = ( k2_setfam_1 @ A @ B ) ) <=>
% 57.95/58.18       ( ![D:$i]:
% 57.95/58.18         ( ( r2_hidden @ D @ C ) <=>
% 57.95/58.18           ( ?[E:$i,F:$i]:
% 57.95/58.18             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 57.95/58.18               ( ( D ) = ( k2_xboole_0 @ E @ F ) ) ) ) ) ) ))).
% 57.95/58.18  thf(zf_stmt_1, axiom,
% 57.95/58.18    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 57.95/58.18     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 57.95/58.18       ( ( ( D ) = ( k2_xboole_0 @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 57.95/58.18         ( r2_hidden @ E @ A ) ) ))).
% 57.95/58.18  thf('11', plain,
% 57.95/58.18      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 57.95/58.18         ((zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X16)
% 57.95/58.18          | ~ (r2_hidden @ X11 @ X16)
% 57.95/58.18          | ~ (r2_hidden @ X12 @ X14)
% 57.95/58.18          | ((X13) != (k2_xboole_0 @ X11 @ X12)))),
% 57.95/58.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 57.95/58.18  thf('12', plain,
% 57.95/58.18      (![X11 : $i, X12 : $i, X14 : $i, X16 : $i]:
% 57.95/58.18         (~ (r2_hidden @ X12 @ X14)
% 57.95/58.18          | ~ (r2_hidden @ X11 @ X16)
% 57.95/58.18          | (zip_tseitin_0 @ X12 @ X11 @ (k2_xboole_0 @ X11 @ X12) @ X14 @ X16))),
% 57.95/58.18      inference('simplify', [status(thm)], ['11'])).
% 57.95/58.18  thf('13', plain,
% 57.95/58.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 57.95/58.18         ((r1_setfam_1 @ X0 @ X1)
% 57.95/58.18          | (zip_tseitin_0 @ (sk_C @ X1 @ X0) @ X3 @ 
% 57.95/58.18             (k2_xboole_0 @ X3 @ (sk_C @ X1 @ X0)) @ X0 @ X2)
% 57.95/58.18          | ~ (r2_hidden @ X3 @ X2))),
% 57.95/58.18      inference('sup-', [status(thm)], ['10', '12'])).
% 57.95/58.18  thf('14', plain,
% 57.95/58.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 57.95/58.18         ((r1_setfam_1 @ X0 @ X1)
% 57.95/58.18          | (zip_tseitin_0 @ (sk_C @ X3 @ X2) @ (sk_C @ X1 @ X0) @ 
% 57.95/58.18             (k2_xboole_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ X2 @ X0)
% 57.95/58.18          | (r1_setfam_1 @ X2 @ X3))),
% 57.95/58.18      inference('sup-', [status(thm)], ['9', '13'])).
% 57.95/58.18  thf('15', plain,
% 57.95/58.18      (![X0 : $i, X1 : $i]:
% 57.95/58.18         ((zip_tseitin_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X1 @ X0) @ 
% 57.95/58.18           (sk_C @ X1 @ X0) @ X0 @ X0)
% 57.95/58.18          | (r1_setfam_1 @ X0 @ X1)
% 57.95/58.18          | (r1_setfam_1 @ X0 @ X1))),
% 57.95/58.18      inference('sup+', [status(thm)], ['8', '14'])).
% 57.95/58.18  thf('16', plain,
% 57.95/58.18      (![X0 : $i, X1 : $i]:
% 57.95/58.18         ((r1_setfam_1 @ X0 @ X1)
% 57.95/58.18          | (zip_tseitin_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X1 @ X0) @ 
% 57.95/58.18             (sk_C @ X1 @ X0) @ X0 @ X0))),
% 57.95/58.18      inference('simplify', [status(thm)], ['15'])).
% 57.95/58.18  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 57.95/58.18  thf(zf_stmt_3, axiom,
% 57.95/58.18    (![A:$i,B:$i,C:$i]:
% 57.95/58.18     ( ( ( C ) = ( k2_setfam_1 @ A @ B ) ) <=>
% 57.95/58.18       ( ![D:$i]:
% 57.95/58.18         ( ( r2_hidden @ D @ C ) <=>
% 57.95/58.18           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 57.95/58.18  thf('17', plain,
% 57.95/58.18      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 57.95/58.18         (~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21)
% 57.95/58.18          | (r2_hidden @ X19 @ X22)
% 57.95/58.18          | ((X22) != (k2_setfam_1 @ X21 @ X20)))),
% 57.95/58.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 57.95/58.18  thf('18', plain,
% 57.95/58.18      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 57.95/58.18         ((r2_hidden @ X19 @ (k2_setfam_1 @ X21 @ X20))
% 57.95/58.18          | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 57.95/58.18      inference('simplify', [status(thm)], ['17'])).
% 57.95/58.18  thf('19', plain,
% 57.95/58.18      (![X0 : $i, X1 : $i]:
% 57.95/58.18         ((r1_setfam_1 @ X0 @ X1)
% 57.95/58.18          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)))),
% 57.95/58.18      inference('sup-', [status(thm)], ['16', '18'])).
% 57.95/58.18  thf(reflexivity_r1_setfam_1, axiom, (![A:$i,B:$i]: ( r1_setfam_1 @ A @ A ))).
% 57.95/58.18  thf('20', plain, (![X27 : $i]: (r1_setfam_1 @ X27 @ X27)),
% 57.95/58.18      inference('cnf', [status(esa)], [reflexivity_r1_setfam_1])).
% 57.95/58.18  thf('21', plain,
% 57.95/58.18      (![X6 : $i, X7 : $i, X8 : $i]:
% 57.95/58.18         ((r2_hidden @ (sk_D_1 @ X6 @ X7) @ X7)
% 57.95/58.18          | ~ (r2_hidden @ X6 @ X8)
% 57.95/58.18          | ~ (r1_setfam_1 @ X8 @ X7))),
% 57.95/58.18      inference('cnf', [status(esa)], [d2_setfam_1])).
% 57.95/58.18  thf('22', plain,
% 57.95/58.18      (![X0 : $i, X1 : $i]:
% 57.95/58.18         (~ (r2_hidden @ X1 @ X0) | (r2_hidden @ (sk_D_1 @ X1 @ X0) @ X0))),
% 57.95/58.18      inference('sup-', [status(thm)], ['20', '21'])).
% 57.95/58.18  thf('23', plain,
% 57.95/58.18      (![X0 : $i, X1 : $i]:
% 57.95/58.18         ((r1_setfam_1 @ X0 @ X1)
% 57.95/58.18          | (r2_hidden @ 
% 57.95/58.18             (sk_D_1 @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)) @ 
% 57.95/58.18             (k2_setfam_1 @ X0 @ X0)))),
% 57.95/58.18      inference('sup-', [status(thm)], ['19', '22'])).
% 57.95/58.18  thf('24', plain, (![X27 : $i]: (r1_setfam_1 @ X27 @ X27)),
% 57.95/58.18      inference('cnf', [status(esa)], [reflexivity_r1_setfam_1])).
% 57.95/58.18  thf('25', plain,
% 57.95/58.18      (![X0 : $i, X1 : $i]:
% 57.95/58.18         ((r1_setfam_1 @ X0 @ X1)
% 57.95/58.18          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)))),
% 57.95/58.18      inference('sup-', [status(thm)], ['16', '18'])).
% 57.95/58.18  thf('26', plain,
% 57.95/58.18      (![X6 : $i, X7 : $i, X8 : $i]:
% 57.95/58.18         ((r1_tarski @ X6 @ (sk_D_1 @ X6 @ X7))
% 57.95/58.18          | ~ (r2_hidden @ X6 @ X8)
% 57.95/58.18          | ~ (r1_setfam_1 @ X8 @ X7))),
% 57.95/58.18      inference('cnf', [status(esa)], [d2_setfam_1])).
% 57.95/58.18  thf('27', plain,
% 57.95/58.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 57.95/58.18         ((r1_setfam_1 @ X0 @ X1)
% 57.95/58.18          | ~ (r1_setfam_1 @ (k2_setfam_1 @ X0 @ X0) @ X2)
% 57.95/58.18          | (r1_tarski @ (sk_C @ X1 @ X0) @ (sk_D_1 @ (sk_C @ X1 @ X0) @ X2)))),
% 57.95/58.18      inference('sup-', [status(thm)], ['25', '26'])).
% 57.95/58.18  thf('28', plain,
% 57.95/58.18      (![X0 : $i, X1 : $i]:
% 57.95/58.18         ((r1_tarski @ (sk_C @ X1 @ X0) @ 
% 57.95/58.18           (sk_D_1 @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)))
% 57.95/58.18          | (r1_setfam_1 @ X0 @ X1))),
% 57.95/58.18      inference('sup-', [status(thm)], ['24', '27'])).
% 57.95/58.18  thf('29', plain,
% 57.95/58.18      (![X8 : $i, X9 : $i, X10 : $i]:
% 57.95/58.18         ((r1_setfam_1 @ X8 @ X9)
% 57.95/58.18          | ~ (r2_hidden @ X10 @ X9)
% 57.95/58.18          | ~ (r1_tarski @ (sk_C @ X9 @ X8) @ X10))),
% 57.95/58.18      inference('cnf', [status(esa)], [d2_setfam_1])).
% 57.95/58.18  thf('30', plain,
% 57.95/58.18      (![X0 : $i, X1 : $i]:
% 57.95/58.18         ((r1_setfam_1 @ X0 @ X1)
% 57.95/58.18          | ~ (r2_hidden @ 
% 57.95/58.18               (sk_D_1 @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)) @ X1)
% 57.95/58.18          | (r1_setfam_1 @ X0 @ X1))),
% 57.95/58.18      inference('sup-', [status(thm)], ['28', '29'])).
% 57.95/58.18  thf('31', plain,
% 57.95/58.18      (![X0 : $i, X1 : $i]:
% 57.95/58.18         (~ (r2_hidden @ 
% 57.95/58.18             (sk_D_1 @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)) @ X1)
% 57.95/58.18          | (r1_setfam_1 @ X0 @ X1))),
% 57.95/58.18      inference('simplify', [status(thm)], ['30'])).
% 57.95/58.18  thf('32', plain,
% 57.95/58.18      (![X0 : $i]:
% 57.95/58.18         ((r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0))
% 57.95/58.18          | (r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0)))),
% 57.95/58.18      inference('sup-', [status(thm)], ['23', '31'])).
% 57.95/58.18  thf('33', plain, (![X0 : $i]: (r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0))),
% 57.95/58.18      inference('simplify', [status(thm)], ['32'])).
% 57.95/58.18  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 57.95/58.18  
% 57.95/58.18  % SZS output end Refutation
% 57.95/58.18  
% 57.95/58.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
