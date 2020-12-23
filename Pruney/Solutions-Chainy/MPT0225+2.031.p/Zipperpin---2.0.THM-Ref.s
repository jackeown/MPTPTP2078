%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ONy5eOeF1w

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  529 ( 768 expanded)
%              Number of equality atoms :   73 ( 114 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('0',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
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

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X9 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X18 ) @ X19 )
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('18',plain,
    ( ( ( ( k1_tarski @ sk_B )
       != ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    ! [X18: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X18 ) @ X20 )
        = ( k1_tarski @ X18 ) )
      | ( r2_hidden @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,
    ( ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,
    ( ( ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,
    ( ( sk_A = sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('37',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_A != sk_B )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','20','21','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ONy5eOeF1w
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:21:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 57 iterations in 0.025s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(t20_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.49         ( k1_tarski @ A ) ) <=>
% 0.21/0.49       ( ( A ) != ( B ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.49            ( k1_tarski @ A ) ) <=>
% 0.21/0.49          ( ( A ) != ( B ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((((sk_A) = (sk_B))
% 0.21/0.49        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49            != (k1_tarski @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((((sk_A) = (sk_B))) | 
% 0.21/0.49       ~
% 0.21/0.49       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49          = (k1_tarski @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf(t69_enumset1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.49  thf('2', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf(t70_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.49  thf(d1_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.49       ( ![E:$i]:
% 0.21/0.49         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.49           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.49  thf(zf_stmt_2, axiom,
% 0.21/0.49    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.49     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.49       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_3, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.49       ( ![E:$i]:
% 0.21/0.49         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.21/0.49          | (r2_hidden @ X5 @ X9)
% 0.21/0.49          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.49         ((r2_hidden @ X5 @ (k1_enumset1 @ X8 @ X7 @ X6))
% 0.21/0.49          | (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 0.21/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.49          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['3', '5'])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (((X1) != (X0)) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X2 : $i, X3 : $i]: ~ (zip_tseitin_0 @ X0 @ X2 @ X3 @ X0)),
% 0.21/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.49  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['2', '9'])).
% 0.21/0.49  thf('11', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((((sk_A) != (sk_B))
% 0.21/0.49        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49            = (k1_tarski @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49          = (k1_tarski @ sk_A)))
% 0.21/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49                = (k1_tarski @ sk_A))))),
% 0.21/0.49      inference('split', [status(esa)], ['12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.21/0.49          = (k1_tarski @ sk_A)))
% 0.21/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49                = (k1_tarski @ sk_A))) & 
% 0.21/0.49             (((sk_A) = (sk_B))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['11', '13'])).
% 0.21/0.49  thf('15', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.21/0.49          = (k1_tarski @ sk_B)))
% 0.21/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49                = (k1_tarski @ sk_A))) & 
% 0.21/0.49             (((sk_A) = (sk_B))))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf(l33_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.49       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X18 @ X19)
% 0.21/0.49          | ((k4_xboole_0 @ (k1_tarski @ X18) @ X19) != (k1_tarski @ X18)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (((((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.21/0.49         | ~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))))
% 0.21/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49                = (k1_tarski @ sk_A))) & 
% 0.21/0.49             (((sk_A) = (sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))
% 0.21/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49                = (k1_tarski @ sk_A))) & 
% 0.21/0.49             (((sk_A) = (sk_B))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (~ (((sk_A) = (sk_B))) | 
% 0.21/0.49       ~
% 0.21/0.49       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49          = (k1_tarski @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (~ (((sk_A) = (sk_B))) | 
% 0.21/0.49       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49          = (k1_tarski @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['12'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.49         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.21/0.49          | ((X1) = (X2))
% 0.21/0.49          | ((X1) = (X3))
% 0.21/0.49          | ((X1) = (X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X18 : $i, X20 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ (k1_tarski @ X18) @ X20) = (k1_tarski @ X18))
% 0.21/0.49          | (r2_hidden @ X18 @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49          != (k1_tarski @ sk_A)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49                = (k1_tarski @ sk_A))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.21/0.49         | (r2_hidden @ sk_A @ (k1_tarski @ sk_B))))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49                = (k1_tarski @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49                = (k1_tarski @ sk_A))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.49          | ~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.21/0.49          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.49         (~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.21/0.49          | ~ (r2_hidden @ X10 @ (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.49          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.21/0.49          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      ((~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49                = (k1_tarski @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B))))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49                = (k1_tarski @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((((sk_A) = (sk_B)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49                = (k1_tarski @ sk_A))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.49  thf('36', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['12'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((((sk_B) != (sk_B)))
% 0.21/0.49         <= (~ (((sk_A) = (sk_B))) & 
% 0.21/0.49             ~
% 0.21/0.49             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49                = (k1_tarski @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      ((((sk_A) = (sk_B))) | 
% 0.21/0.49       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49          = (k1_tarski @ sk_A)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.49  thf('39', plain, ($false),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['1', '20', '21', '38'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
