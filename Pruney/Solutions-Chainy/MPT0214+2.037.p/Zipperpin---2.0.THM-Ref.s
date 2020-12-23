%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zVDopHvXzl

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:49 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   58 (  77 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  381 ( 551 expanded)
%              Number of equality atoms :   42 (  60 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

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

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

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
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,(
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

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('11',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X49
        = ( k1_tarski @ X48 ) )
      | ( X49 = k1_xboole_0 )
      | ~ ( r1_tarski @ X49 @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('12',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_B )
      | ( X0 = sk_B )
      | ( X0 = sk_B )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( sk_A = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('26',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('27',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('33',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('sup-',[status(thm)],['26','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zVDopHvXzl
% 0.13/0.37  % Computer   : n011.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 20:35:42 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.24/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.52  % Solved by: fo/fo7.sh
% 0.24/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.52  % done 76 iterations in 0.036s
% 0.24/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.52  % SZS output start Refutation
% 0.24/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.24/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.24/0.52  thf(t69_enumset1, axiom,
% 0.24/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.52  thf('0', plain, (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.24/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.52  thf(t70_enumset1, axiom,
% 0.24/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.24/0.52  thf('1', plain,
% 0.24/0.52      (![X21 : $i, X22 : $i]:
% 0.24/0.52         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.24/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.24/0.52  thf(d1_enumset1, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.24/0.52       ( ![E:$i]:
% 0.24/0.52         ( ( r2_hidden @ E @ D ) <=>
% 0.24/0.52           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.24/0.52  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.24/0.52  thf(zf_stmt_1, axiom,
% 0.24/0.52    (![E:$i,C:$i,B:$i,A:$i]:
% 0.24/0.52     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.24/0.52       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.24/0.52  thf(zf_stmt_2, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.24/0.52       ( ![E:$i]:
% 0.24/0.52         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.24/0.52  thf('2', plain,
% 0.24/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.24/0.52         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.24/0.52          | (r2_hidden @ X13 @ X17)
% 0.24/0.52          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.24/0.52  thf('3', plain,
% 0.24/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.52         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.24/0.52          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.24/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.24/0.52  thf('4', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.52         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.24/0.52          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.24/0.52      inference('sup+', [status(thm)], ['1', '3'])).
% 0.24/0.52  thf('5', plain,
% 0.24/0.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.24/0.52         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.24/0.52  thf('6', plain,
% 0.24/0.52      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X8)),
% 0.24/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.24/0.52  thf('7', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.24/0.52      inference('sup-', [status(thm)], ['4', '6'])).
% 0.24/0.52  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.24/0.52      inference('sup+', [status(thm)], ['0', '7'])).
% 0.24/0.52  thf('9', plain,
% 0.24/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.24/0.52         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.24/0.52          | ((X9) = (X10))
% 0.24/0.52          | ((X9) = (X11))
% 0.24/0.52          | ((X9) = (X12)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.24/0.52  thf(t6_zfmisc_1, conjecture,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.24/0.52       ( ( A ) = ( B ) ) ))).
% 0.24/0.52  thf(zf_stmt_3, negated_conjecture,
% 0.24/0.52    (~( ![A:$i,B:$i]:
% 0.24/0.52        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.24/0.52          ( ( A ) = ( B ) ) ) )),
% 0.24/0.52    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.24/0.52  thf('10', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.24/0.52  thf(l3_zfmisc_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.24/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.24/0.53  thf('11', plain,
% 0.24/0.53      (![X48 : $i, X49 : $i]:
% 0.24/0.53         (((X49) = (k1_tarski @ X48))
% 0.24/0.53          | ((X49) = (k1_xboole_0))
% 0.24/0.53          | ~ (r1_tarski @ X49 @ (k1_tarski @ X48)))),
% 0.24/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.24/0.53  thf('12', plain,
% 0.24/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.24/0.53        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.53  thf('13', plain,
% 0.24/0.53      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.24/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.53  thf('14', plain,
% 0.24/0.53      (![X21 : $i, X22 : $i]:
% 0.24/0.53         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.24/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.24/0.53  thf('15', plain,
% 0.24/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X18 @ X17)
% 0.24/0.53          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.24/0.53          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.24/0.53  thf('16', plain,
% 0.24/0.53      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.24/0.53         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.24/0.53          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.24/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.24/0.53  thf('17', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.24/0.53          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.24/0.53      inference('sup-', [status(thm)], ['14', '16'])).
% 0.24/0.53  thf('18', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.24/0.53          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['13', '17'])).
% 0.24/0.53  thf('19', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.24/0.53          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.24/0.53          | ~ (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B))),
% 0.24/0.53      inference('sup-', [status(thm)], ['12', '18'])).
% 0.24/0.53  thf('20', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (((X0) = (sk_B))
% 0.24/0.53          | ((X0) = (sk_B))
% 0.24/0.53          | ((X0) = (sk_B))
% 0.24/0.53          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.24/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['9', '19'])).
% 0.24/0.53  thf('21', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.24/0.53          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.24/0.53          | ((X0) = (sk_B)))),
% 0.24/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.24/0.53  thf('22', plain,
% 0.24/0.53      ((((sk_A) = (sk_B)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['8', '21'])).
% 0.24/0.53  thf('23', plain, (((sk_A) != (sk_B))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.24/0.53  thf('24', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.24/0.53      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.24/0.53  thf('25', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.24/0.53      inference('sup+', [status(thm)], ['0', '7'])).
% 0.24/0.53  thf('26', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.24/0.53      inference('sup+', [status(thm)], ['24', '25'])).
% 0.24/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.24/0.53  thf('27', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.24/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.24/0.53  thf(d7_xboole_0, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.24/0.53       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.53  thf('28', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.24/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.24/0.53  thf('29', plain,
% 0.24/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.24/0.53  thf(t4_xboole_0, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.24/0.53  thf('30', plain,
% 0.24/0.53      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.24/0.53          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.24/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.24/0.53  thf('31', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.24/0.53  thf('32', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.24/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.24/0.53  thf('33', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.24/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.24/0.53  thf('34', plain, ($false), inference('sup-', [status(thm)], ['26', '33'])).
% 0.24/0.53  
% 0.24/0.53  % SZS output end Refutation
% 0.24/0.53  
% 0.24/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
