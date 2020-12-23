%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nCMGHUlTG2

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:18 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   51 (  57 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  343 ( 398 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t47_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t47_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X17 @ X21 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nCMGHUlTG2
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:15:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.72  % Solved by: fo/fo7.sh
% 0.46/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.72  % done 408 iterations in 0.277s
% 0.46/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.72  % SZS output start Refutation
% 0.46/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.72  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.72  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.46/0.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.72  thf(t47_zfmisc_1, conjecture,
% 0.46/0.72    (![A:$i,B:$i,C:$i]:
% 0.46/0.72     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.46/0.72       ( r2_hidden @ A @ C ) ))).
% 0.46/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.72        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.46/0.72          ( r2_hidden @ A @ C ) ) )),
% 0.46/0.72    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.46/0.72  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.72  thf(t70_enumset1, axiom,
% 0.46/0.72    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.72  thf('1', plain,
% 0.46/0.72      (![X24 : $i, X25 : $i]:
% 0.46/0.72         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.46/0.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.72  thf(d1_enumset1, axiom,
% 0.46/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.72     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.72       ( ![E:$i]:
% 0.46/0.72         ( ( r2_hidden @ E @ D ) <=>
% 0.46/0.72           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.46/0.72  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.46/0.72  thf(zf_stmt_2, axiom,
% 0.46/0.72    (![E:$i,C:$i,B:$i,A:$i]:
% 0.46/0.72     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.46/0.72       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.46/0.72  thf(zf_stmt_3, axiom,
% 0.46/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.72     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.72       ( ![E:$i]:
% 0.46/0.72         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.46/0.72  thf('2', plain,
% 0.46/0.72      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.72         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.46/0.72          | (r2_hidden @ X17 @ X21)
% 0.46/0.72          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.72  thf('3', plain,
% 0.46/0.72      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.72         ((r2_hidden @ X17 @ (k1_enumset1 @ X20 @ X19 @ X18))
% 0.46/0.72          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20))),
% 0.46/0.72      inference('simplify', [status(thm)], ['2'])).
% 0.46/0.72  thf('4', plain,
% 0.46/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.72         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.72          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.46/0.72      inference('sup+', [status(thm)], ['1', '3'])).
% 0.46/0.72  thf('5', plain,
% 0.46/0.72      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.72         (((X13) != (X12)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.72  thf('6', plain,
% 0.46/0.72      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.46/0.72         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X12)),
% 0.46/0.72      inference('simplify', [status(thm)], ['5'])).
% 0.46/0.72  thf('7', plain,
% 0.46/0.72      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.46/0.72      inference('sup-', [status(thm)], ['4', '6'])).
% 0.46/0.72  thf(d3_tarski, axiom,
% 0.46/0.72    (![A:$i,B:$i]:
% 0.46/0.72     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.72  thf('8', plain,
% 0.46/0.72      (![X1 : $i, X3 : $i]:
% 0.46/0.72         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.72  thf(d3_xboole_0, axiom,
% 0.46/0.72    (![A:$i,B:$i,C:$i]:
% 0.46/0.72     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.46/0.72       ( ![D:$i]:
% 0.46/0.72         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.72           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.46/0.72  thf('9', plain,
% 0.46/0.72      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.72         (~ (r2_hidden @ X4 @ X5)
% 0.46/0.72          | (r2_hidden @ X4 @ X6)
% 0.46/0.72          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.46/0.72      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.46/0.72  thf('10', plain,
% 0.46/0.72      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.46/0.72         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.46/0.72      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.72  thf('11', plain,
% 0.46/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.72         ((r1_tarski @ X0 @ X1)
% 0.46/0.72          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.46/0.72      inference('sup-', [status(thm)], ['8', '10'])).
% 0.46/0.72  thf('12', plain,
% 0.46/0.72      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) @ sk_C_1)),
% 0.46/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.72  thf('13', plain,
% 0.46/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.72         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.72          | (r2_hidden @ X0 @ X2)
% 0.46/0.72          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.72  thf('14', plain,
% 0.46/0.72      (![X0 : $i]:
% 0.46/0.72         ((r2_hidden @ X0 @ sk_C_1)
% 0.46/0.72          | ~ (r2_hidden @ X0 @ 
% 0.46/0.72               (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.46/0.72      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.72  thf(commutativity_k2_tarski, axiom,
% 0.46/0.72    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.72  thf('15', plain,
% 0.46/0.72      (![X10 : $i, X11 : $i]:
% 0.46/0.72         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.46/0.72      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.72  thf(l51_zfmisc_1, axiom,
% 0.46/0.72    (![A:$i,B:$i]:
% 0.46/0.72     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.72  thf('16', plain,
% 0.46/0.72      (![X29 : $i, X30 : $i]:
% 0.46/0.72         ((k3_tarski @ (k2_tarski @ X29 @ X30)) = (k2_xboole_0 @ X29 @ X30))),
% 0.46/0.72      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.72  thf('17', plain,
% 0.46/0.72      (![X0 : $i, X1 : $i]:
% 0.46/0.72         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.72      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.72  thf('18', plain,
% 0.46/0.72      (![X29 : $i, X30 : $i]:
% 0.46/0.72         ((k3_tarski @ (k2_tarski @ X29 @ X30)) = (k2_xboole_0 @ X29 @ X30))),
% 0.46/0.72      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.72  thf('19', plain,
% 0.46/0.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.72      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.72  thf('20', plain,
% 0.46/0.72      (![X0 : $i]:
% 0.46/0.72         ((r2_hidden @ X0 @ sk_C_1)
% 0.46/0.72          | ~ (r2_hidden @ X0 @ 
% 0.46/0.72               (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.46/0.72      inference('demod', [status(thm)], ['14', '19'])).
% 0.46/0.72  thf('21', plain,
% 0.46/0.72      (![X0 : $i]:
% 0.46/0.72         ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.46/0.72          | (r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ sk_C_1))),
% 0.46/0.72      inference('sup-', [status(thm)], ['11', '20'])).
% 0.46/0.72  thf('22', plain,
% 0.46/0.72      (![X1 : $i, X3 : $i]:
% 0.46/0.72         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.46/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.72  thf('23', plain,
% 0.46/0.72      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.46/0.72        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.46/0.72      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.72  thf('24', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.46/0.72      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.72  thf('25', plain,
% 0.46/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.72         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.72          | (r2_hidden @ X0 @ X2)
% 0.46/0.72          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.72  thf('26', plain,
% 0.46/0.72      (![X0 : $i]:
% 0.46/0.72         ((r2_hidden @ X0 @ sk_C_1)
% 0.46/0.72          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.46/0.72      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.72  thf('27', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.46/0.72      inference('sup-', [status(thm)], ['7', '26'])).
% 0.46/0.72  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.46/0.72  
% 0.46/0.72  % SZS output end Refutation
% 0.46/0.72  
% 0.55/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
