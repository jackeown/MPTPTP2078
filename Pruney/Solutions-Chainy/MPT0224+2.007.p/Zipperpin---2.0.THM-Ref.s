%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UNPdVS8H4P

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:44 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  438 ( 519 expanded)
%              Number of equality atoms :   40 (  48 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t19_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t19_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
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

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','24'])).

thf('26',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UNPdVS8H4P
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.60/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.77  % Solved by: fo/fo7.sh
% 0.60/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.77  % done 285 iterations in 0.274s
% 0.60/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.77  % SZS output start Refutation
% 0.60/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.60/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.77  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.60/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.60/0.77  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.60/0.77  thf(t19_zfmisc_1, conjecture,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.60/0.77       ( k1_tarski @ A ) ))).
% 0.60/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.77    (~( ![A:$i,B:$i]:
% 0.60/0.77        ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.60/0.77          ( k1_tarski @ A ) ) )),
% 0.60/0.77    inference('cnf.neg', [status(esa)], [t19_zfmisc_1])).
% 0.60/0.77  thf('0', plain,
% 0.60/0.77      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.60/0.77         != (k1_tarski @ sk_A))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(t70_enumset1, axiom,
% 0.60/0.77    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.60/0.77  thf('1', plain,
% 0.60/0.77      (![X21 : $i, X22 : $i]:
% 0.60/0.77         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.60/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.60/0.77  thf(d1_enumset1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.77     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.60/0.77       ( ![E:$i]:
% 0.60/0.77         ( ( r2_hidden @ E @ D ) <=>
% 0.60/0.77           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.60/0.77  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.60/0.77  thf(zf_stmt_2, axiom,
% 0.60/0.77    (![E:$i,C:$i,B:$i,A:$i]:
% 0.60/0.77     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.60/0.77       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.60/0.77  thf(zf_stmt_3, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.77     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.60/0.77       ( ![E:$i]:
% 0.60/0.77         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.60/0.77  thf('2', plain,
% 0.60/0.77      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.60/0.77         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.60/0.77          | (r2_hidden @ X13 @ X17)
% 0.60/0.77          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('3', plain,
% 0.60/0.77      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.77         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.60/0.77          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.60/0.77      inference('simplify', [status(thm)], ['2'])).
% 0.60/0.77  thf('4', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.77         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.60/0.77          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.60/0.77      inference('sup+', [status(thm)], ['1', '3'])).
% 0.60/0.77  thf('5', plain,
% 0.60/0.77      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.77         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.77  thf('6', plain,
% 0.60/0.77      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X8)),
% 0.60/0.77      inference('simplify', [status(thm)], ['5'])).
% 0.60/0.77  thf('7', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.60/0.77      inference('sup-', [status(thm)], ['4', '6'])).
% 0.60/0.77  thf('8', plain,
% 0.60/0.77      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.77         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.60/0.77          | ((X9) = (X10))
% 0.60/0.77          | ((X9) = (X11))
% 0.60/0.77          | ((X9) = (X12)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.77  thf(d4_xboole_0, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i]:
% 0.60/0.77     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.60/0.77       ( ![D:$i]:
% 0.60/0.77         ( ( r2_hidden @ D @ C ) <=>
% 0.60/0.77           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.60/0.77  thf('9', plain,
% 0.60/0.77      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.60/0.77         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.60/0.77          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.60/0.77          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.60/0.77      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.60/0.77  thf('10', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.60/0.77          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.60/0.77      inference('eq_fact', [status(thm)], ['9'])).
% 0.60/0.77  thf(t69_enumset1, axiom,
% 0.60/0.77    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.60/0.77  thf('11', plain,
% 0.60/0.77      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.60/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.77  thf('12', plain,
% 0.60/0.77      (![X21 : $i, X22 : $i]:
% 0.60/0.77         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.60/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.60/0.77  thf('13', plain,
% 0.60/0.77      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X18 @ X17)
% 0.60/0.77          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.60/0.77          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('14', plain,
% 0.60/0.77      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.60/0.77         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.60/0.77          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['13'])).
% 0.60/0.77  thf('15', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.60/0.77          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.60/0.77      inference('sup-', [status(thm)], ['12', '14'])).
% 0.60/0.77  thf('16', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.60/0.77          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['11', '15'])).
% 0.60/0.77  thf('17', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.60/0.77          | ~ (zip_tseitin_0 @ 
% 0.60/0.77               (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['10', '16'])).
% 0.60/0.77  thf('18', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.60/0.77          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.60/0.77          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.60/0.77          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['8', '17'])).
% 0.60/0.77  thf('19', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.60/0.77          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['18'])).
% 0.60/0.77  thf('20', plain,
% 0.60/0.77      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.60/0.77         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.60/0.77          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.60/0.77          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.60/0.77          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.60/0.77      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.60/0.77  thf('21', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X0 @ X1)
% 0.60/0.77          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.60/0.77          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 0.60/0.77               (k1_tarski @ X0))
% 0.60/0.77          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 0.60/0.77               (k1_tarski @ X0))
% 0.60/0.77          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['19', '20'])).
% 0.60/0.77  thf('22', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 0.60/0.77             (k1_tarski @ X0))
% 0.60/0.77          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.60/0.77          | ~ (r2_hidden @ X0 @ X1))),
% 0.60/0.77      inference('simplify', [status(thm)], ['21'])).
% 0.60/0.77  thf('23', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.60/0.77          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.60/0.77      inference('eq_fact', [status(thm)], ['9'])).
% 0.60/0.77  thf('24', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X0 @ X1)
% 0.60/0.77          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.60/0.77      inference('clc', [status(thm)], ['22', '23'])).
% 0.60/0.77  thf('25', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k1_tarski @ X1)
% 0.60/0.77           = (k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['7', '24'])).
% 0.60/0.77  thf('26', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.60/0.77      inference('demod', [status(thm)], ['0', '25'])).
% 0.60/0.77  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.60/0.77  
% 0.60/0.77  % SZS output end Refutation
% 0.60/0.77  
% 0.60/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
