%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VrUV06nzb5

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:05 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   42 (  50 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  325 ( 398 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_setfam_1_type,type,(
    k2_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_setfam_1 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_setfam_1 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X8 ) ) ),
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

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X16 )
      | ~ ( r2_hidden @ X11 @ X16 )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ( X13
       != ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X11: $i,X12: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X11 @ X16 )
      | ( zip_tseitin_0 @ X12 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) @ X14 @ X16 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C_1 @ X1 @ X0 ) @ X3 @ ( k2_xboole_0 @ X3 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C_1 @ X3 @ X2 ) @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C_1 @ X3 @ X2 ) ) @ X2 @ X0 )
      | ( r1_setfam_1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) @ X0 @ X0 )
      | ( r1_setfam_1 @ X0 @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

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

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X19 @ X22 )
      | ( X22
       != ( k2_setfam_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X19 @ ( k2_setfam_1 @ X21 @ X20 ) )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_setfam_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X9 @ X8 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) )
      | ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VrUV06nzb5
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:47:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.54/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.77  % Solved by: fo/fo7.sh
% 0.54/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.77  % done 137 iterations in 0.324s
% 0.54/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.77  % SZS output start Refutation
% 0.54/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.77  thf(k2_setfam_1_type, type, k2_setfam_1: $i > $i > $i).
% 0.54/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.77  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.54/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.54/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.77  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.54/0.77  thf(t29_setfam_1, conjecture,
% 0.54/0.77    (![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ))).
% 0.54/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.77    (~( ![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) )),
% 0.54/0.77    inference('cnf.neg', [status(esa)], [t29_setfam_1])).
% 0.54/0.77  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ (k2_setfam_1 @ sk_A @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(d3_tarski, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( r1_tarski @ A @ B ) <=>
% 0.54/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.54/0.77  thf('1', plain,
% 0.54/0.77      (![X1 : $i, X3 : $i]:
% 0.54/0.77         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.54/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.77  thf('2', plain,
% 0.54/0.77      (![X1 : $i, X3 : $i]:
% 0.54/0.77         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.54/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.77  thf('3', plain,
% 0.54/0.77      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.77  thf('4', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.54/0.77      inference('simplify', [status(thm)], ['3'])).
% 0.54/0.77  thf(t12_xboole_1, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.54/0.77  thf('5', plain,
% 0.54/0.77      (![X4 : $i, X5 : $i]:
% 0.54/0.77         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.54/0.77      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.54/0.77  thf('6', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.77  thf(d2_setfam_1, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.54/0.77       ( ![C:$i]:
% 0.54/0.77         ( ~( ( r2_hidden @ C @ A ) & 
% 0.54/0.77              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.54/0.77  thf('7', plain,
% 0.54/0.77      (![X8 : $i, X9 : $i]:
% 0.54/0.77         ((r1_setfam_1 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X8))),
% 0.54/0.77      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.54/0.77  thf('8', plain,
% 0.54/0.77      (![X8 : $i, X9 : $i]:
% 0.54/0.77         ((r1_setfam_1 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X8))),
% 0.54/0.77      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.54/0.77  thf(d4_setfam_1, axiom,
% 0.54/0.77    (![A:$i,B:$i,C:$i]:
% 0.54/0.77     ( ( ( C ) = ( k2_setfam_1 @ A @ B ) ) <=>
% 0.54/0.77       ( ![D:$i]:
% 0.54/0.77         ( ( r2_hidden @ D @ C ) <=>
% 0.54/0.77           ( ?[E:$i,F:$i]:
% 0.54/0.77             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.54/0.77               ( ( D ) = ( k2_xboole_0 @ E @ F ) ) ) ) ) ) ))).
% 0.61/0.77  thf(zf_stmt_1, axiom,
% 0.61/0.77    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.61/0.77     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.61/0.77       ( ( ( D ) = ( k2_xboole_0 @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.61/0.77         ( r2_hidden @ E @ A ) ) ))).
% 0.61/0.77  thf('9', plain,
% 0.61/0.77      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.61/0.77         ((zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X16)
% 0.61/0.77          | ~ (r2_hidden @ X11 @ X16)
% 0.61/0.77          | ~ (r2_hidden @ X12 @ X14)
% 0.61/0.77          | ((X13) != (k2_xboole_0 @ X11 @ X12)))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.77  thf('10', plain,
% 0.61/0.77      (![X11 : $i, X12 : $i, X14 : $i, X16 : $i]:
% 0.61/0.77         (~ (r2_hidden @ X12 @ X14)
% 0.61/0.77          | ~ (r2_hidden @ X11 @ X16)
% 0.61/0.77          | (zip_tseitin_0 @ X12 @ X11 @ (k2_xboole_0 @ X11 @ X12) @ X14 @ X16))),
% 0.61/0.77      inference('simplify', [status(thm)], ['9'])).
% 0.61/0.77  thf('11', plain,
% 0.61/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.61/0.77         ((r1_setfam_1 @ X0 @ X1)
% 0.61/0.77          | (zip_tseitin_0 @ (sk_C_1 @ X1 @ X0) @ X3 @ 
% 0.61/0.77             (k2_xboole_0 @ X3 @ (sk_C_1 @ X1 @ X0)) @ X0 @ X2)
% 0.61/0.77          | ~ (r2_hidden @ X3 @ X2))),
% 0.61/0.77      inference('sup-', [status(thm)], ['8', '10'])).
% 0.61/0.77  thf('12', plain,
% 0.61/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.61/0.77         ((r1_setfam_1 @ X0 @ X1)
% 0.61/0.77          | (zip_tseitin_0 @ (sk_C_1 @ X3 @ X2) @ (sk_C_1 @ X1 @ X0) @ 
% 0.61/0.77             (k2_xboole_0 @ (sk_C_1 @ X1 @ X0) @ (sk_C_1 @ X3 @ X2)) @ X2 @ X0)
% 0.61/0.77          | (r1_setfam_1 @ X2 @ X3))),
% 0.61/0.77      inference('sup-', [status(thm)], ['7', '11'])).
% 0.61/0.77  thf('13', plain,
% 0.61/0.77      (![X0 : $i, X1 : $i]:
% 0.61/0.77         ((zip_tseitin_0 @ (sk_C_1 @ X1 @ X0) @ (sk_C_1 @ X1 @ X0) @ 
% 0.61/0.77           (sk_C_1 @ X1 @ X0) @ X0 @ X0)
% 0.61/0.77          | (r1_setfam_1 @ X0 @ X1)
% 0.61/0.77          | (r1_setfam_1 @ X0 @ X1))),
% 0.61/0.77      inference('sup+', [status(thm)], ['6', '12'])).
% 0.61/0.77  thf('14', plain,
% 0.61/0.77      (![X0 : $i, X1 : $i]:
% 0.61/0.77         ((r1_setfam_1 @ X0 @ X1)
% 0.61/0.77          | (zip_tseitin_0 @ (sk_C_1 @ X1 @ X0) @ (sk_C_1 @ X1 @ X0) @ 
% 0.61/0.77             (sk_C_1 @ X1 @ X0) @ X0 @ X0))),
% 0.61/0.77      inference('simplify', [status(thm)], ['13'])).
% 0.61/0.77  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.61/0.77  thf(zf_stmt_3, axiom,
% 0.61/0.77    (![A:$i,B:$i,C:$i]:
% 0.61/0.77     ( ( ( C ) = ( k2_setfam_1 @ A @ B ) ) <=>
% 0.61/0.77       ( ![D:$i]:
% 0.61/0.77         ( ( r2_hidden @ D @ C ) <=>
% 0.61/0.77           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.61/0.77  thf('15', plain,
% 0.61/0.77      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.61/0.77         (~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.61/0.77          | (r2_hidden @ X19 @ X22)
% 0.61/0.77          | ((X22) != (k2_setfam_1 @ X21 @ X20)))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.77  thf('16', plain,
% 0.61/0.77      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.61/0.77         ((r2_hidden @ X19 @ (k2_setfam_1 @ X21 @ X20))
% 0.61/0.77          | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.61/0.77      inference('simplify', [status(thm)], ['15'])).
% 0.61/0.77  thf('17', plain,
% 0.61/0.77      (![X0 : $i, X1 : $i]:
% 0.61/0.77         ((r1_setfam_1 @ X0 @ X1)
% 0.61/0.77          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)))),
% 0.61/0.77      inference('sup-', [status(thm)], ['14', '16'])).
% 0.61/0.77  thf('18', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.61/0.77      inference('simplify', [status(thm)], ['3'])).
% 0.61/0.77  thf('19', plain,
% 0.61/0.77      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.61/0.77         ((r1_setfam_1 @ X8 @ X9)
% 0.61/0.77          | ~ (r2_hidden @ X10 @ X9)
% 0.61/0.77          | ~ (r1_tarski @ (sk_C_1 @ X9 @ X8) @ X10))),
% 0.61/0.77      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.61/0.77  thf('20', plain,
% 0.61/0.77      (![X0 : $i, X1 : $i]:
% 0.61/0.77         (~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1) | (r1_setfam_1 @ X0 @ X1))),
% 0.61/0.77      inference('sup-', [status(thm)], ['18', '19'])).
% 0.61/0.77  thf('21', plain,
% 0.61/0.77      (![X0 : $i]:
% 0.61/0.77         ((r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0))
% 0.61/0.77          | (r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0)))),
% 0.61/0.77      inference('sup-', [status(thm)], ['17', '20'])).
% 0.61/0.77  thf('22', plain, (![X0 : $i]: (r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0))),
% 0.61/0.77      inference('simplify', [status(thm)], ['21'])).
% 0.61/0.77  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.61/0.77  
% 0.61/0.77  % SZS output end Refutation
% 0.61/0.77  
% 0.61/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
