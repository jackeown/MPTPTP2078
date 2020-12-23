%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cYKnZNsUlr

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:06 EST 2020

% Result     : Theorem 51.61s
% Output     : Refutation 51.61s
% Verified   : 
% Statistics : Number of formulae       :   53 (  85 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :  588 (1081 expanded)
%              Number of equality atoms :   53 (  87 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t144_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
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

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k2_tarski @ X1 @ X0 ) @ X2 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k2_tarski @ X0 @ X1 ) @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X1 ) @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X1 ) @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( ( k2_tarski @ X0 @ X1 )
        = ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X0 @ X1 )
        = ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ X2 ) )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X1 ) @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X1 ) @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( sk_D @ ( k2_tarski @ X2 @ X0 ) @ X1 @ ( k2_tarski @ X2 @ X0 ) )
        = X2 )
      | ( ( k2_tarski @ X2 @ X0 )
        = ( k4_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ X1 ) )
      | ( ( k2_tarski @ X2 @ X0 )
        = ( k4_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X2 @ X0 )
        = ( k4_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k2_tarski @ X2 @ X0 ) @ X1 @ ( k2_tarski @ X2 @ X0 ) )
        = X2 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X2 @ X1 )
      | ( ( k2_tarski @ X0 @ X2 )
        = ( k4_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 ) )
      | ( ( k2_tarski @ X0 @ X2 )
        = ( k4_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X0 @ X2 )
        = ( k4_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 ) )
      | ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cYKnZNsUlr
% 0.15/0.36  % Computer   : n015.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 14:35:23 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 51.61/51.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 51.61/51.87  % Solved by: fo/fo7.sh
% 51.61/51.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 51.61/51.87  % done 17129 iterations in 51.397s
% 51.61/51.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 51.61/51.87  % SZS output start Refutation
% 51.61/51.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 51.61/51.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 51.61/51.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 51.61/51.87  thf(sk_B_type, type, sk_B: $i).
% 51.61/51.87  thf(sk_C_type, type, sk_C: $i).
% 51.61/51.87  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 51.61/51.87  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 51.61/51.87  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 51.61/51.87  thf(sk_A_type, type, sk_A: $i).
% 51.61/51.87  thf(t144_zfmisc_1, conjecture,
% 51.61/51.87    (![A:$i,B:$i,C:$i]:
% 51.61/51.87     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 51.61/51.87          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 51.61/51.87  thf(zf_stmt_0, negated_conjecture,
% 51.61/51.87    (~( ![A:$i,B:$i,C:$i]:
% 51.61/51.87        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 51.61/51.87             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 51.61/51.87    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 51.61/51.87  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 51.61/51.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.61/51.87  thf(d1_enumset1, axiom,
% 51.61/51.87    (![A:$i,B:$i,C:$i,D:$i]:
% 51.61/51.87     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 51.61/51.87       ( ![E:$i]:
% 51.61/51.87         ( ( r2_hidden @ E @ D ) <=>
% 51.61/51.87           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 51.61/51.87  thf(zf_stmt_1, axiom,
% 51.61/51.87    (![E:$i,C:$i,B:$i,A:$i]:
% 51.61/51.87     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 51.61/51.87       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 51.61/51.87  thf('1', plain,
% 51.61/51.87      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 51.61/51.87         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 51.61/51.87          | ((X9) = (X10))
% 51.61/51.87          | ((X9) = (X11))
% 51.61/51.87          | ((X9) = (X12)))),
% 51.61/51.87      inference('cnf', [status(esa)], [zf_stmt_1])).
% 51.61/51.87  thf(d5_xboole_0, axiom,
% 51.61/51.87    (![A:$i,B:$i,C:$i]:
% 51.61/51.87     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 51.61/51.87       ( ![D:$i]:
% 51.61/51.87         ( ( r2_hidden @ D @ C ) <=>
% 51.61/51.87           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 51.61/51.87  thf('2', plain,
% 51.61/51.87      (![X1 : $i, X2 : $i, X5 : $i]:
% 51.61/51.87         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 51.61/51.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 51.61/51.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 51.61/51.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 51.61/51.87  thf('3', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i]:
% 51.61/51.87         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 51.61/51.87          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 51.61/51.87      inference('eq_fact', [status(thm)], ['2'])).
% 51.61/51.87  thf(t70_enumset1, axiom,
% 51.61/51.87    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 51.61/51.87  thf('4', plain,
% 51.61/51.87      (![X20 : $i, X21 : $i]:
% 51.61/51.87         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 51.61/51.87      inference('cnf', [status(esa)], [t70_enumset1])).
% 51.61/51.87  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 51.61/51.87  thf(zf_stmt_3, axiom,
% 51.61/51.87    (![A:$i,B:$i,C:$i,D:$i]:
% 51.61/51.87     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 51.61/51.87       ( ![E:$i]:
% 51.61/51.87         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 51.61/51.87  thf('5', plain,
% 51.61/51.87      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 51.61/51.87         (~ (r2_hidden @ X18 @ X17)
% 51.61/51.87          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 51.61/51.87          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 51.61/51.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 51.61/51.87  thf('6', plain,
% 51.61/51.87      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 51.61/51.87         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 51.61/51.87          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 51.61/51.87      inference('simplify', [status(thm)], ['5'])).
% 51.61/51.87  thf('7', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.61/51.87         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 51.61/51.87          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 51.61/51.87      inference('sup-', [status(thm)], ['4', '6'])).
% 51.61/51.87  thf('8', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.61/51.87         (((k2_tarski @ X1 @ X0) = (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2))
% 51.61/51.87          | ~ (zip_tseitin_0 @ 
% 51.61/51.87               (sk_D @ (k2_tarski @ X1 @ X0) @ X2 @ (k2_tarski @ X1 @ X0)) @ 
% 51.61/51.87               X0 @ X1 @ X1))),
% 51.61/51.87      inference('sup-', [status(thm)], ['3', '7'])).
% 51.61/51.87  thf('9', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.61/51.87         (((sk_D @ (k2_tarski @ X0 @ X1) @ X2 @ (k2_tarski @ X0 @ X1)) = (X0))
% 51.61/51.87          | ((sk_D @ (k2_tarski @ X0 @ X1) @ X2 @ (k2_tarski @ X0 @ X1)) = (X0))
% 51.61/51.87          | ((sk_D @ (k2_tarski @ X0 @ X1) @ X2 @ (k2_tarski @ X0 @ X1)) = (X1))
% 51.61/51.87          | ((k2_tarski @ X0 @ X1) = (k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ X2)))),
% 51.61/51.87      inference('sup-', [status(thm)], ['1', '8'])).
% 51.61/51.87  thf('10', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.61/51.87         (((k2_tarski @ X0 @ X1) = (k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ X2))
% 51.61/51.87          | ((sk_D @ (k2_tarski @ X0 @ X1) @ X2 @ (k2_tarski @ X0 @ X1)) = (X1))
% 51.61/51.87          | ((sk_D @ (k2_tarski @ X0 @ X1) @ X2 @ (k2_tarski @ X0 @ X1)) = (X0)))),
% 51.61/51.87      inference('simplify', [status(thm)], ['9'])).
% 51.61/51.87  thf('11', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i]:
% 51.61/51.87         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 51.61/51.87          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 51.61/51.87      inference('eq_fact', [status(thm)], ['2'])).
% 51.61/51.87  thf('12', plain,
% 51.61/51.87      (![X1 : $i, X2 : $i, X5 : $i]:
% 51.61/51.87         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 51.61/51.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 51.61/51.87          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 51.61/51.87          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 51.61/51.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 51.61/51.87  thf('13', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i]:
% 51.61/51.87         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 51.61/51.87          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 51.61/51.87          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 51.61/51.87          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 51.61/51.87      inference('sup-', [status(thm)], ['11', '12'])).
% 51.61/51.87  thf('14', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i]:
% 51.61/51.87         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 51.61/51.87          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 51.61/51.87          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 51.61/51.87      inference('simplify', [status(thm)], ['13'])).
% 51.61/51.87  thf('15', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i]:
% 51.61/51.87         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 51.61/51.87          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 51.61/51.87      inference('eq_fact', [status(thm)], ['2'])).
% 51.61/51.87  thf('16', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i]:
% 51.61/51.87         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 51.61/51.87          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 51.61/51.87      inference('clc', [status(thm)], ['14', '15'])).
% 51.61/51.87  thf('17', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.61/51.87         ((r2_hidden @ X0 @ X1)
% 51.61/51.87          | ((sk_D @ (k2_tarski @ X2 @ X0) @ X1 @ (k2_tarski @ X2 @ X0)) = (X2))
% 51.61/51.87          | ((k2_tarski @ X2 @ X0) = (k4_xboole_0 @ (k2_tarski @ X2 @ X0) @ X1))
% 51.61/51.87          | ((k2_tarski @ X2 @ X0) = (k4_xboole_0 @ (k2_tarski @ X2 @ X0) @ X1)))),
% 51.61/51.87      inference('sup+', [status(thm)], ['10', '16'])).
% 51.61/51.87  thf('18', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.61/51.87         (((k2_tarski @ X2 @ X0) = (k4_xboole_0 @ (k2_tarski @ X2 @ X0) @ X1))
% 51.61/51.87          | ((sk_D @ (k2_tarski @ X2 @ X0) @ X1 @ (k2_tarski @ X2 @ X0)) = (X2))
% 51.61/51.87          | (r2_hidden @ X0 @ X1))),
% 51.61/51.87      inference('simplify', [status(thm)], ['17'])).
% 51.61/51.87  thf('19', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i]:
% 51.61/51.87         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 51.61/51.87          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 51.61/51.87      inference('clc', [status(thm)], ['14', '15'])).
% 51.61/51.87  thf('20', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.61/51.87         ((r2_hidden @ X0 @ X1)
% 51.61/51.87          | (r2_hidden @ X2 @ X1)
% 51.61/51.87          | ((k2_tarski @ X0 @ X2) = (k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1))
% 51.61/51.87          | ((k2_tarski @ X0 @ X2) = (k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1)))),
% 51.61/51.87      inference('sup+', [status(thm)], ['18', '19'])).
% 51.61/51.87  thf('21', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.61/51.87         (((k2_tarski @ X0 @ X2) = (k4_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1))
% 51.61/51.87          | (r2_hidden @ X2 @ X1)
% 51.61/51.87          | (r2_hidden @ X0 @ X1))),
% 51.61/51.87      inference('simplify', [status(thm)], ['20'])).
% 51.61/51.87  thf('22', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i]:
% 51.61/51.87         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 51.61/51.87          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 51.61/51.87      inference('eq_fact', [status(thm)], ['2'])).
% 51.61/51.87  thf('23', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i]:
% 51.61/51.87         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 51.61/51.87          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 51.61/51.87      inference('clc', [status(thm)], ['14', '15'])).
% 51.61/51.87  thf('24', plain,
% 51.61/51.87      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 51.61/51.87         (~ (r2_hidden @ X4 @ X3)
% 51.61/51.87          | ~ (r2_hidden @ X4 @ X2)
% 51.61/51.87          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 51.61/51.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 51.61/51.87  thf('25', plain,
% 51.61/51.87      (![X1 : $i, X2 : $i, X4 : $i]:
% 51.61/51.87         (~ (r2_hidden @ X4 @ X2)
% 51.61/51.87          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 51.61/51.87      inference('simplify', [status(thm)], ['24'])).
% 51.61/51.87  thf('26', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.61/51.87         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 51.61/51.87          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 51.61/51.87      inference('sup-', [status(thm)], ['23', '25'])).
% 51.61/51.87  thf('27', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i]:
% 51.61/51.87         (((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 51.61/51.87          | ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 51.61/51.87      inference('sup-', [status(thm)], ['22', '26'])).
% 51.61/51.87  thf('28', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i]:
% 51.61/51.87         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 51.61/51.87      inference('simplify', [status(thm)], ['27'])).
% 51.61/51.87  thf('29', plain,
% 51.61/51.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.61/51.87         (((X2) = (k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))
% 51.61/51.87          | (r2_hidden @ X1 @ X2)
% 51.61/51.87          | (r2_hidden @ X0 @ X2))),
% 51.61/51.87      inference('sup+', [status(thm)], ['21', '28'])).
% 51.61/51.87  thf('30', plain,
% 51.61/51.87      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 51.61/51.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.61/51.87  thf('31', plain,
% 51.61/51.87      ((((sk_C) != (sk_C))
% 51.61/51.87        | (r2_hidden @ sk_B @ sk_C)
% 51.61/51.87        | (r2_hidden @ sk_A @ sk_C))),
% 51.61/51.87      inference('sup-', [status(thm)], ['29', '30'])).
% 51.61/51.87  thf('32', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 51.61/51.87      inference('simplify', [status(thm)], ['31'])).
% 51.61/51.87  thf('33', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 51.61/51.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.61/51.87  thf('34', plain, ((r2_hidden @ sk_B @ sk_C)),
% 51.61/51.87      inference('clc', [status(thm)], ['32', '33'])).
% 51.61/51.87  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 51.61/51.87  
% 51.61/51.87  % SZS output end Refutation
% 51.61/51.87  
% 51.61/51.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
