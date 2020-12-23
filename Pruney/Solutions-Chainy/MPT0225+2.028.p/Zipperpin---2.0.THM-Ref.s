%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KKtxFuUHlN

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
% Statistics : Number of formulae       :   62 (  81 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  540 ( 744 expanded)
%              Number of equality atoms :   67 ( 102 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( r2_hidden @ X10 @ X14 )
      | ( X14
       != ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ ( k1_enumset1 @ X13 @ X12 @ X11 ) )
      | ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X5 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ~ ( zip_tseitin_0 @ X5 @ X7 @ X8 @ X5 ) ),
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

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k4_xboole_0 @ X2 @ X4 )
       != X2 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('15',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 )
      | ( X6 = X7 )
      | ( X6 = X8 )
      | ( X6 = X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('23',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X29 ) @ X30 )
      | ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X11 @ X12 @ X13 )
      | ( X14
       != ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X11 @ X12 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,
    ( ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,
    ( ( ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,
    ( ( sk_A = sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('39',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_A != sk_B )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','20','21','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KKtxFuUHlN
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 114 iterations in 0.036s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(t20_zfmisc_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.46         ( k1_tarski @ A ) ) <=>
% 0.21/0.46       ( ( A ) != ( B ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.46            ( k1_tarski @ A ) ) <=>
% 0.21/0.46          ( ( A ) != ( B ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      ((((sk_A) = (sk_B))
% 0.21/0.46        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46            != (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      ((((sk_A) = (sk_B))) | 
% 0.21/0.46       ~
% 0.21/0.46       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46          = (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf(t69_enumset1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.46  thf('2', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.21/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.46  thf(t70_enumset1, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X18 : $i, X19 : $i]:
% 0.21/0.46         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.21/0.46      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.46  thf(d1_enumset1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.46       ( ![E:$i]:
% 0.21/0.46         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.46           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.46  thf(zf_stmt_2, axiom,
% 0.21/0.46    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.46     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.46       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_3, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.46       ( ![E:$i]:
% 0.21/0.46         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.46         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.21/0.46          | (r2_hidden @ X10 @ X14)
% 0.21/0.46          | ((X14) != (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.46         ((r2_hidden @ X10 @ (k1_enumset1 @ X13 @ X12 @ X11))
% 0.21/0.46          | (zip_tseitin_0 @ X10 @ X11 @ X12 @ X13))),
% 0.21/0.46      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.46          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.46      inference('sup+', [status(thm)], ['3', '5'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.46         (((X6) != (X5)) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X5 : $i, X7 : $i, X8 : $i]: ~ (zip_tseitin_0 @ X5 @ X7 @ X8 @ X5)),
% 0.21/0.46      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.46  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['2', '9'])).
% 0.21/0.46  thf('11', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      ((((sk_A) != (sk_B))
% 0.21/0.46        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46            = (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46          = (k1_tarski @ sk_A)))
% 0.21/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46                = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('split', [status(esa)], ['12'])).
% 0.21/0.46  thf(t83_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (![X2 : $i, X4 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ X2 @ X4) | ((k4_xboole_0 @ X2 @ X4) != (X2)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.21/0.46         | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))
% 0.21/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46                = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.21/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46                = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.46  thf(l24_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X27 : $i, X28 : $i]:
% 0.21/0.46         (~ (r1_xboole_0 @ (k1_tarski @ X27) @ X28) | ~ (r2_hidden @ X27 @ X28))),
% 0.21/0.46      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46                = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))
% 0.21/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46                = (k1_tarski @ sk_A))) & 
% 0.21/0.46             (((sk_A) = (sk_B))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['11', '18'])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      (~ (((sk_A) = (sk_B))) | 
% 0.21/0.46       ~
% 0.21/0.46       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46          = (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['10', '19'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (~ (((sk_A) = (sk_B))) | 
% 0.21/0.46       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46          = (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['12'])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.46         ((zip_tseitin_0 @ X6 @ X7 @ X8 @ X9)
% 0.21/0.46          | ((X6) = (X7))
% 0.21/0.46          | ((X6) = (X8))
% 0.21/0.46          | ((X6) = (X9)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.46  thf(l27_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      (![X29 : $i, X30 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ (k1_tarski @ X29) @ X30) | (r2_hidden @ X29 @ X30))),
% 0.21/0.46      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.46  thf('24', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i]:
% 0.21/0.46         (((k4_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.21/0.46      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.46  thf('25', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((r2_hidden @ X1 @ X0)
% 0.21/0.46          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.46  thf('26', plain,
% 0.21/0.46      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46          != (k1_tarski @ sk_A)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46                = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('27', plain,
% 0.21/0.46      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.21/0.46         | (r2_hidden @ sk_A @ (k1_tarski @ sk_B))))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46                = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.46  thf('28', plain,
% 0.21/0.46      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46                = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.46  thf('29', plain,
% 0.21/0.46      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.21/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.46  thf('30', plain,
% 0.21/0.46      (![X18 : $i, X19 : $i]:
% 0.21/0.46         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.21/0.46      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.46  thf('31', plain,
% 0.21/0.46      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X15 @ X14)
% 0.21/0.46          | ~ (zip_tseitin_0 @ X15 @ X11 @ X12 @ X13)
% 0.21/0.46          | ((X14) != (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.46  thf('32', plain,
% 0.21/0.46      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 0.21/0.46         (~ (zip_tseitin_0 @ X15 @ X11 @ X12 @ X13)
% 0.21/0.46          | ~ (r2_hidden @ X15 @ (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.46  thf('33', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.46          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.46      inference('sup-', [status(thm)], ['30', '32'])).
% 0.21/0.46  thf('34', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.21/0.46          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['29', '33'])).
% 0.21/0.46  thf('35', plain,
% 0.21/0.46      ((~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46                = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['28', '34'])).
% 0.21/0.46  thf('36', plain,
% 0.21/0.46      (((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B))))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46                = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['22', '35'])).
% 0.21/0.46  thf('37', plain,
% 0.21/0.46      ((((sk_A) = (sk_B)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46                = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.46  thf('38', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.21/0.46      inference('split', [status(esa)], ['12'])).
% 0.21/0.46  thf('39', plain,
% 0.21/0.46      ((((sk_B) != (sk_B)))
% 0.21/0.46         <= (~ (((sk_A) = (sk_B))) & 
% 0.21/0.46             ~
% 0.21/0.46             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46                = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.46  thf('40', plain,
% 0.21/0.46      ((((sk_A) = (sk_B))) | 
% 0.21/0.46       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.46          = (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.46  thf('41', plain, ($false),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['1', '20', '21', '40'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
