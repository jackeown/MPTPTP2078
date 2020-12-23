%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l7hQVQIBEh

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 (  97 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  452 ( 765 expanded)
%              Number of equality atoms :   44 (  70 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('11',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('12',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31
        = ( k1_tarski @ X30 ) )
      | ( X31 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('13',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_B )
      | ( X0 = sk_B )
      | ( X0 = sk_B )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( sk_A = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('31',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ( ( k4_xboole_0 @ X5 @ X7 )
       != X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['29','40'])).

thf('42',plain,(
    $false ),
    inference('sup-',[status(thm)],['6','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l7hQVQIBEh
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:48:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 211 iterations in 0.113s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(t70_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (![X21 : $i, X22 : $i]:
% 0.21/0.57         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.21/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.57  thf(d1_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.57       ( ![E:$i]:
% 0.21/0.57         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.57           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_1, axiom,
% 0.21/0.57    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.57     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.57       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.57       ( ![E:$i]:
% 0.21/0.57         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.57         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.21/0.57          | (r2_hidden @ X13 @ X17)
% 0.21/0.57          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.57         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.21/0.57          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.21/0.57      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.57          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.57      inference('sup+', [status(thm)], ['0', '2'])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.57         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X8)),
% 0.21/0.57      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.57  thf(t69_enumset1, axiom,
% 0.21/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.57  thf('7', plain, (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.21/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.57  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.57         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.21/0.57          | ((X9) = (X10))
% 0.21/0.57          | ((X9) = (X11))
% 0.21/0.57          | ((X9) = (X12)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.57  thf(t6_zfmisc_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.57       ( ( A ) = ( B ) ) ))).
% 0.21/0.57  thf(zf_stmt_3, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i]:
% 0.21/0.57        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.57          ( ( A ) = ( B ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.21/0.57  thf('11', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.57  thf(l3_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X30 : $i, X31 : $i]:
% 0.21/0.57         (((X31) = (k1_tarski @ X30))
% 0.21/0.57          | ((X31) = (k1_xboole_0))
% 0.21/0.57          | ~ (r1_tarski @ X31 @ (k1_tarski @ X30)))),
% 0.21/0.57      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.57        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.21/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X21 : $i, X22 : $i]:
% 0.21/0.57         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.21/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X18 @ X17)
% 0.21/0.57          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.21/0.57          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.21/0.57         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.21/0.57          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.57          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['15', '17'])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.21/0.57          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '18'])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.21/0.57          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.57          | ~ (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['13', '19'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (sk_B))
% 0.21/0.57          | ((X0) = (sk_B))
% 0.21/0.57          | ((X0) = (sk_B))
% 0.21/0.57          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['10', '20'])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.21/0.57          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.57          | ((X0) = (sk_B)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      ((((sk_A) = (sk_B)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['9', '22'])).
% 0.21/0.57  thf('24', plain, (((sk_A) != (sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.57  thf('25', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.21/0.57  thf('26', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf(t3_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.57            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.57          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.57          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['25', '28'])).
% 0.21/0.57  thf(t3_boole, axiom,
% 0.21/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.57  thf('30', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.57  thf(t83_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (![X5 : $i, X7 : $i]:
% 0.21/0.57         ((r1_xboole_0 @ X5 @ X7) | ((k4_xboole_0 @ X5 @ X7) != (X5)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.57  thf('33', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.21/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.57          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.57          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.57          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.57          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.21/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.57          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.21/0.57          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['34', '37'])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.57  thf('40', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.57      inference('sup-', [status(thm)], ['33', '39'])).
% 0.21/0.57  thf('41', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '40'])).
% 0.21/0.57  thf('42', plain, ($false), inference('sup-', [status(thm)], ['6', '41'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
