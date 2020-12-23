%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6EsYOyW8TX

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 100 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  364 ( 757 expanded)
%              Number of equality atoms :   46 (  95 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t24_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27
        = ( k1_tarski @ X26 ) )
      | ( X27 = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
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

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
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

thf('20',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf('22',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_B = sk_A ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('25',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X30 ) )
      | ( X29 != X30 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('26',plain,(
    ! [X30: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_xboole_0 @ X1 @ X3 )
      | ( ( k4_xboole_0 @ X1 @ X3 )
       != X1 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6EsYOyW8TX
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:10:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 77 iterations in 0.038s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(d1_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.51       ( ![E:$i]:
% 0.22/0.51         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.51           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, axiom,
% 0.22/0.51    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.51     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.51       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.51         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.22/0.51          | ((X5) = (X6))
% 0.22/0.51          | ((X5) = (X7))
% 0.22/0.51          | ((X5) = (X8)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t24_zfmisc_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.22/0.51       ( ( A ) = ( B ) ) ))).
% 0.22/0.51  thf(zf_stmt_1, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i]:
% 0.22/0.51        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.22/0.51          ( ( A ) = ( B ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t24_zfmisc_1])).
% 0.22/0.51  thf('1', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.51  thf(l3_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.22/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X26 : $i, X27 : $i]:
% 0.22/0.51         (((X27) = (k1_tarski @ X26))
% 0.22/0.51          | ((X27) = (k1_xboole_0))
% 0.22/0.51          | ~ (r1_tarski @ X27 @ (k1_tarski @ X26)))),
% 0.22/0.51      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.51        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf(t69_enumset1, axiom,
% 0.22/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.51  thf('4', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf(t70_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X17 : $i, X18 : $i]:
% 0.22/0.51         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.22/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.51  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_3, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.51       ( ![E:$i]:
% 0.22/0.51         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.51         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.22/0.51          | (r2_hidden @ X9 @ X13)
% 0.22/0.51          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.51         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.22/0.51          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.22/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.51          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.51      inference('sup+', [status(thm)], ['5', '7'])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.51         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.22/0.52      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['8', '10'])).
% 0.22/0.52  thf('12', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['4', '11'])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.22/0.52        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['3', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i]:
% 0.22/0.52         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.22/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X14 @ X13)
% 0.22/0.52          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.22/0.52          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.22/0.52         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.22/0.52          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.52          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['15', '17'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.52          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.52        | ~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      ((((sk_B) = (sk_A))
% 0.22/0.52        | ((sk_B) = (sk_A))
% 0.22/0.52        | ((sk_B) = (sk_A))
% 0.22/0.52        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '20'])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_B) = (sk_A)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.52  thf('23', plain, (((sk_A) != (sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.52  thf('24', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf(t16_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.22/0.52          ( ( A ) = ( B ) ) ) ))).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X29 : $i, X30 : $i]:
% 0.22/0.52         (~ (r1_xboole_0 @ (k1_tarski @ X29) @ (k1_tarski @ X30))
% 0.22/0.52          | ((X29) != (X30)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X30 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X30))),
% 0.22/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.52  thf('27', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '26'])).
% 0.22/0.52  thf('28', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf(t3_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.52  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.52  thf(t83_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X1 : $i, X3 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X1 @ X3) | ((k4_xboole_0 @ X1 @ X3) != (X1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.22/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.52  thf('33', plain, ($false),
% 0.22/0.52      inference('demod', [status(thm)], ['27', '28', '32'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
