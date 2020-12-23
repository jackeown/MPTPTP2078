%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dt8aBRwRHZ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  95 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   18
%              Number of atoms          :  522 (1035 expanded)
%              Number of equality atoms :   71 ( 159 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t41_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A
           != ( k1_tarski @ B ) )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( C != B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_zfmisc_1])).

thf('1',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ X44 @ sk_A )
      | ( X44 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( sk_B @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['4'])).

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

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X15: $i] :
      ( ( X15
        = ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ~ ( zip_tseitin_0 @ ( sk_E @ X15 @ X10 @ X11 @ X12 ) @ X10 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_E @ X15 @ X10 @ X11 @ X12 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_E @ X3 @ X2 @ X1 @ X0 )
        = X0 )
      | ( ( sk_E @ X3 @ X2 @ X1 @ X0 )
        = X1 )
      | ( ( sk_E @ X3 @ X2 @ X1 @ X0 )
        = X2 )
      | ( r2_hidden @ ( sk_E @ X3 @ X2 @ X1 @ X0 ) @ X3 )
      | ( X3
        = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ X44 @ sk_A )
      | ( X44 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A
        = ( k1_enumset1 @ X0 @ X1 @ X2 ) )
      | ( ( sk_E @ sk_A @ X2 @ X1 @ X0 )
        = X2 )
      | ( ( sk_E @ sk_A @ X2 @ X1 @ X0 )
        = X1 )
      | ( ( sk_E @ sk_A @ X2 @ X1 @ X0 )
        = X0 )
      | ( ( sk_E @ sk_A @ X2 @ X1 @ X0 )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != sk_B_1 )
      | ( ( sk_E @ sk_A @ X0 @ X2 @ X1 )
        = sk_B_1 )
      | ( ( sk_E @ sk_A @ X0 @ X2 @ X1 )
        = X1 )
      | ( ( sk_E @ sk_A @ X0 @ X2 @ X1 )
        = X2 )
      | ( sk_A
        = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( sk_A
        = ( k1_enumset1 @ X1 @ X2 @ sk_B_1 ) )
      | ( ( sk_E @ sk_A @ sk_B_1 @ X2 @ X1 )
        = X2 )
      | ( ( sk_E @ sk_A @ sk_B_1 @ X2 @ X1 )
        = X1 )
      | ( ( sk_E @ sk_A @ sk_B_1 @ X2 @ X1 )
        = sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_B_1 )
      | ( ( sk_E @ sk_A @ sk_B_1 @ X0 @ X1 )
        = sk_B_1 )
      | ( ( sk_E @ sk_A @ sk_B_1 @ X0 @ X1 )
        = X1 )
      | ( sk_A
        = ( k1_enumset1 @ X1 @ X0 @ sk_B_1 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,(
    ! [X1: $i] :
      ( ( sk_A
        = ( k1_enumset1 @ X1 @ sk_B_1 @ sk_B_1 ) )
      | ( ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ X1 )
        = X1 )
      | ( ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ X1 )
        = sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_enumset1 @ X0 @ sk_B_1 @ sk_B_1 ) ) ) ),
    inference(eq_fact,[status(thm)],['14'])).

thf('16',plain,
    ( ( sk_A
      = ( k1_enumset1 @ sk_B_1 @ sk_B_1 @ sk_B_1 ) )
    | ( ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1 )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1 )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i,X15: $i] :
      ( ( X15
        = ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ ( sk_E @ X15 @ X10 @ X11 @ X12 ) @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ ( sk_E @ X15 @ X10 @ X11 @ X12 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_B_1 )
    | ( sk_A
      = ( k1_enumset1 @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1 )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('26',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1 )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('31',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['29','31'])).

thf('33',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','32'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dt8aBRwRHZ
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 121 iterations in 0.062s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(d1_xboole_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.51  thf(t41_zfmisc_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51             ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t41_zfmisc_1])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X44 : $i]: (~ (r2_hidden @ X44 @ sk_A) | ((X44) = (sk_B_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('2', plain, (((v1_xboole_0 @ sk_A) | ((sk_B @ sk_A) = (sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (((r2_hidden @ sk_B_1 @ sk_A)
% 0.20/0.51        | (v1_xboole_0 @ sk_A)
% 0.20/0.51        | (v1_xboole_0 @ sk_A))),
% 0.20/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('5', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B_1 @ sk_A))),
% 0.20/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.51  thf(d1_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.51       ( ![E:$i]:
% 0.20/0.51         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.51           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_1, axiom,
% 0.20/0.51    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.51       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.51         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.20/0.51          | ((X5) = (X6))
% 0.20/0.51          | ((X5) = (X7))
% 0.20/0.51          | ((X5) = (X8)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_3, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.51       ( ![E:$i]:
% 0.20/0.51         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i, X12 : $i, X15 : $i]:
% 0.20/0.51         (((X15) = (k1_enumset1 @ X12 @ X11 @ X10))
% 0.20/0.51          | ~ (zip_tseitin_0 @ (sk_E @ X15 @ X10 @ X11 @ X12) @ X10 @ X11 @ X12)
% 0.20/0.51          | (r2_hidden @ (sk_E @ X15 @ X10 @ X11 @ X12) @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (((sk_E @ X3 @ X2 @ X1 @ X0) = (X0))
% 0.20/0.51          | ((sk_E @ X3 @ X2 @ X1 @ X0) = (X1))
% 0.20/0.51          | ((sk_E @ X3 @ X2 @ X1 @ X0) = (X2))
% 0.20/0.51          | (r2_hidden @ (sk_E @ X3 @ X2 @ X1 @ X0) @ X3)
% 0.20/0.51          | ((X3) = (k1_enumset1 @ X0 @ X1 @ X2)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X44 : $i]: (~ (r2_hidden @ X44 @ sk_A) | ((X44) = (sk_B_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (((sk_A) = (k1_enumset1 @ X0 @ X1 @ X2))
% 0.20/0.51          | ((sk_E @ sk_A @ X2 @ X1 @ X0) = (X2))
% 0.20/0.51          | ((sk_E @ sk_A @ X2 @ X1 @ X0) = (X1))
% 0.20/0.51          | ((sk_E @ sk_A @ X2 @ X1 @ X0) = (X0))
% 0.20/0.51          | ((sk_E @ sk_A @ X2 @ X1 @ X0) = (sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (((X0) != (sk_B_1))
% 0.20/0.51          | ((sk_E @ sk_A @ X0 @ X2 @ X1) = (sk_B_1))
% 0.20/0.51          | ((sk_E @ sk_A @ X0 @ X2 @ X1) = (X1))
% 0.20/0.51          | ((sk_E @ sk_A @ X0 @ X2 @ X1) = (X2))
% 0.20/0.51          | ((sk_A) = (k1_enumset1 @ X1 @ X2 @ X0)))),
% 0.20/0.51      inference('eq_fact', [status(thm)], ['10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         (((sk_A) = (k1_enumset1 @ X1 @ X2 @ sk_B_1))
% 0.20/0.51          | ((sk_E @ sk_A @ sk_B_1 @ X2 @ X1) = (X2))
% 0.20/0.51          | ((sk_E @ sk_A @ sk_B_1 @ X2 @ X1) = (X1))
% 0.20/0.51          | ((sk_E @ sk_A @ sk_B_1 @ X2 @ X1) = (sk_B_1)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) != (sk_B_1))
% 0.20/0.51          | ((sk_E @ sk_A @ sk_B_1 @ X0 @ X1) = (sk_B_1))
% 0.20/0.51          | ((sk_E @ sk_A @ sk_B_1 @ X0 @ X1) = (X1))
% 0.20/0.51          | ((sk_A) = (k1_enumset1 @ X1 @ X0 @ sk_B_1)))),
% 0.20/0.51      inference('eq_fact', [status(thm)], ['12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X1 : $i]:
% 0.20/0.51         (((sk_A) = (k1_enumset1 @ X1 @ sk_B_1 @ sk_B_1))
% 0.20/0.51          | ((sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ X1) = (X1))
% 0.20/0.51          | ((sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ X1) = (sk_B_1)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((sk_B_1) != (X0))
% 0.20/0.51          | ((sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ X0) = (X0))
% 0.20/0.51          | ((sk_A) = (k1_enumset1 @ X0 @ sk_B_1 @ sk_B_1)))),
% 0.20/0.51      inference('eq_fact', [status(thm)], ['14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      ((((sk_A) = (k1_enumset1 @ sk_B_1 @ sk_B_1 @ sk_B_1))
% 0.20/0.51        | ((sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1) = (sk_B_1)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.51  thf(t70_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.51  thf(t69_enumset1, axiom,
% 0.20/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.20/0.51        | ((sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1) = (sk_B_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.51  thf('20', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('21', plain, (((sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1) = (sk_B_1))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i, X12 : $i, X15 : $i]:
% 0.20/0.51         (((X15) = (k1_enumset1 @ X12 @ X11 @ X10))
% 0.20/0.51          | (zip_tseitin_0 @ (sk_E @ X15 @ X10 @ X11 @ X12) @ X10 @ X11 @ X12)
% 0.20/0.51          | ~ (r2_hidden @ (sk_E @ X15 @ X10 @ X11 @ X12) @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.20/0.51        | (zip_tseitin_0 @ (sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1) @ sk_B_1 @ 
% 0.20/0.51           sk_B_1 @ sk_B_1)
% 0.20/0.51        | ((sk_A) = (k1_enumset1 @ sk_B_1 @ sk_B_1 @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf('24', plain, (((sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1) = (sk_B_1))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.20/0.51        | (zip_tseitin_0 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1)
% 0.20/0.51        | ((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.20/0.51  thf('28', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.20/0.51        | (zip_tseitin_0 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.20/0.51      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.51  thf('32', plain, (~ (r2_hidden @ sk_B_1 @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['29', '31'])).
% 0.20/0.51  thf('33', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '32'])).
% 0.20/0.51  thf(l13_xboole_0, axiom,
% 0.20/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.51  thf('35', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('37', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
