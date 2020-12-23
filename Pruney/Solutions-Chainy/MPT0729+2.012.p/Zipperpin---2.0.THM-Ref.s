%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4xkReY06pp

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:42 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   56 (  77 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  369 ( 565 expanded)
%              Number of equality atoms :   39 (  64 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('1',plain,(
    ! [X29: $i] :
      ( r2_hidden @ X29 @ ( k1_ordinal1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(t12_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k1_ordinal1 @ A )
        = ( k1_ordinal1 @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k1_ordinal1 @ A )
          = ( k1_ordinal1 @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_ordinal1])).

thf('2',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('3',plain,(
    ! [X28: $i] :
      ( ( k1_ordinal1 @ X28 )
      = ( k2_xboole_0 @ X28 @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('5',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X29: $i] :
      ( r2_hidden @ X29 @ ( k1_ordinal1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
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

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('25',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['8','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('30',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','30'])).

thf('32',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4xkReY06pp
% 0.15/0.37  % Computer   : n012.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 15:59:07 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 784 iterations in 0.306s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.59/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.79  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.59/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.59/0.79  thf(d1_enumset1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.59/0.79       ( ![E:$i]:
% 0.59/0.79         ( ( r2_hidden @ E @ D ) <=>
% 0.59/0.79           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, axiom,
% 0.59/0.79    (![E:$i,C:$i,B:$i,A:$i]:
% 0.59/0.79     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.59/0.79       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.59/0.79  thf('0', plain,
% 0.59/0.79      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.79         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.59/0.79          | ((X9) = (X10))
% 0.59/0.79          | ((X9) = (X11))
% 0.59/0.79          | ((X9) = (X12)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.59/0.79  thf('1', plain, (![X29 : $i]: (r2_hidden @ X29 @ (k1_ordinal1 @ X29))),
% 0.59/0.79      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.59/0.79  thf(t12_ordinal1, conjecture,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ))).
% 0.59/0.79  thf(zf_stmt_1, negated_conjecture,
% 0.59/0.79    (~( ![A:$i,B:$i]:
% 0.59/0.79        ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t12_ordinal1])).
% 0.59/0.79  thf('2', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.79  thf(d1_ordinal1, axiom,
% 0.59/0.79    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      (![X28 : $i]:
% 0.59/0.79         ((k1_ordinal1 @ X28) = (k2_xboole_0 @ X28 @ (k1_tarski @ X28)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.59/0.79  thf(d3_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.59/0.79       ( ![D:$i]:
% 0.59/0.79         ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.79           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X6 @ X4)
% 0.59/0.79          | (r2_hidden @ X6 @ X5)
% 0.59/0.79          | (r2_hidden @ X6 @ X3)
% 0.59/0.79          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.59/0.79  thf('5', plain,
% 0.59/0.79      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.59/0.79         ((r2_hidden @ X6 @ X3)
% 0.59/0.79          | (r2_hidden @ X6 @ X5)
% 0.59/0.79          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['4'])).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.59/0.79          | (r2_hidden @ X1 @ X0)
% 0.59/0.79          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['3', '5'])).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))
% 0.59/0.79          | (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.59/0.79          | (r2_hidden @ X0 @ sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['2', '6'])).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['1', '7'])).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.79         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.59/0.79          | ((X9) = (X10))
% 0.59/0.79          | ((X9) = (X11))
% 0.59/0.79          | ((X9) = (X12)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('10', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.79  thf('11', plain, (![X29 : $i]: (r2_hidden @ X29 @ (k1_ordinal1 @ X29))),
% 0.59/0.79      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.59/0.79  thf('12', plain, ((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['10', '11'])).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.59/0.79          | (r2_hidden @ X1 @ X0)
% 0.59/0.79          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['3', '5'])).
% 0.59/0.79  thf('14', plain,
% 0.59/0.79      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf(t69_enumset1, axiom,
% 0.59/0.79    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.59/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.79  thf(t70_enumset1, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      (![X21 : $i, X22 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.59/0.79      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.79  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.59/0.79  thf(zf_stmt_3, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.59/0.79       ( ![E:$i]:
% 0.59/0.79         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X18 @ X17)
% 0.59/0.79          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.59/0.79          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.59/0.79         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.59/0.79          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['17'])).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.59/0.79          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['16', '18'])).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.59/0.79          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['15', '19'])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (((r2_hidden @ sk_B @ sk_A)
% 0.59/0.79        | ~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['14', '20'])).
% 0.59/0.79  thf('22', plain,
% 0.59/0.79      ((((sk_B) = (sk_A))
% 0.59/0.79        | ((sk_B) = (sk_A))
% 0.59/0.79        | ((sk_B) = (sk_A))
% 0.59/0.79        | (r2_hidden @ sk_B @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['9', '21'])).
% 0.59/0.79  thf('23', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['22'])).
% 0.59/0.79  thf('24', plain, (((sk_A) != (sk_B))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.79  thf('25', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.59/0.79  thf(antisymmetry_r2_hidden, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.59/0.79  thf('26', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.59/0.79      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.59/0.79  thf('27', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.59/0.79      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.79  thf('28', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.59/0.79      inference('clc', [status(thm)], ['8', '27'])).
% 0.59/0.79  thf('29', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.59/0.79          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['15', '19'])).
% 0.59/0.79  thf('30', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.59/0.79      inference('sup-', [status(thm)], ['28', '29'])).
% 0.59/0.79  thf('31', plain,
% 0.59/0.79      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['0', '30'])).
% 0.59/0.79  thf('32', plain, (((sk_A) = (sk_B))),
% 0.59/0.79      inference('simplify', [status(thm)], ['31'])).
% 0.59/0.79  thf('33', plain, (((sk_A) != (sk_B))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.79  thf('34', plain, ($false),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.64/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
