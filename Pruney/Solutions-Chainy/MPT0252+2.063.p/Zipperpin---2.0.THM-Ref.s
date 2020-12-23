%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rksi5Ze5Bb

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:25 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  274 ( 330 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X51: $i,X52: $i] :
      ( ( k1_enumset1 @ X51 @ X51 @ X52 )
      = ( k2_tarski @ X51 @ X52 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X33 @ X37 )
      | ( X37
       != ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X33 @ ( k1_enumset1 @ X36 @ X35 @ X34 ) )
      | ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X29 != X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ~ ( zip_tseitin_0 @ X28 @ X30 @ X31 @ X28 ) ),
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
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rksi5Ze5Bb
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:23:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.69/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.88  % Solved by: fo/fo7.sh
% 0.69/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.88  % done 722 iterations in 0.418s
% 0.69/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.88  % SZS output start Refutation
% 0.69/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.88  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.69/0.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.69/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.88  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.69/0.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.69/0.88  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.69/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.88  thf(t47_zfmisc_1, conjecture,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.69/0.88       ( r2_hidden @ A @ C ) ))).
% 0.69/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.88    (~( ![A:$i,B:$i,C:$i]:
% 0.69/0.88        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.69/0.88          ( r2_hidden @ A @ C ) ) )),
% 0.69/0.88    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.69/0.88  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(t70_enumset1, axiom,
% 0.69/0.88    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.69/0.88  thf('1', plain,
% 0.69/0.88      (![X51 : $i, X52 : $i]:
% 0.69/0.88         ((k1_enumset1 @ X51 @ X51 @ X52) = (k2_tarski @ X51 @ X52))),
% 0.69/0.88      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.69/0.88  thf(d1_enumset1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.88     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.69/0.88       ( ![E:$i]:
% 0.69/0.88         ( ( r2_hidden @ E @ D ) <=>
% 0.69/0.88           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.69/0.88  thf(zf_stmt_2, axiom,
% 0.69/0.88    (![E:$i,C:$i,B:$i,A:$i]:
% 0.69/0.88     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.69/0.88       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_3, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.88     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.69/0.88       ( ![E:$i]:
% 0.69/0.88         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.69/0.88  thf('2', plain,
% 0.69/0.88      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.69/0.88         ((zip_tseitin_0 @ X33 @ X34 @ X35 @ X36)
% 0.69/0.88          | (r2_hidden @ X33 @ X37)
% 0.69/0.88          | ((X37) != (k1_enumset1 @ X36 @ X35 @ X34)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.69/0.88  thf('3', plain,
% 0.69/0.88      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.69/0.88         ((r2_hidden @ X33 @ (k1_enumset1 @ X36 @ X35 @ X34))
% 0.69/0.88          | (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36))),
% 0.69/0.88      inference('simplify', [status(thm)], ['2'])).
% 0.69/0.88  thf('4', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.69/0.88          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['1', '3'])).
% 0.69/0.88  thf('5', plain,
% 0.69/0.88      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.69/0.88         (((X29) != (X28)) | ~ (zip_tseitin_0 @ X29 @ X30 @ X31 @ X28))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.69/0.88  thf('6', plain,
% 0.69/0.88      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.69/0.88         ~ (zip_tseitin_0 @ X28 @ X30 @ X31 @ X28)),
% 0.69/0.88      inference('simplify', [status(thm)], ['5'])).
% 0.69/0.88  thf('7', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.69/0.88      inference('sup-', [status(thm)], ['4', '6'])).
% 0.69/0.88  thf(d3_tarski, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( r1_tarski @ A @ B ) <=>
% 0.69/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.69/0.88  thf('8', plain,
% 0.69/0.88      (![X3 : $i, X5 : $i]:
% 0.69/0.88         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.69/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.88  thf(t7_xboole_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.69/0.88  thf('9', plain,
% 0.69/0.88      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.69/0.88      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.69/0.88  thf('10', plain,
% 0.69/0.88      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X2 @ X3)
% 0.69/0.88          | (r2_hidden @ X2 @ X4)
% 0.69/0.88          | ~ (r1_tarski @ X3 @ X4))),
% 0.69/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.88  thf('11', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.69/0.88      inference('sup-', [status(thm)], ['9', '10'])).
% 0.69/0.88  thf('12', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((r1_tarski @ X0 @ X1)
% 0.69/0.88          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['8', '11'])).
% 0.69/0.88  thf('13', plain,
% 0.69/0.88      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) @ sk_C_1)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('14', plain,
% 0.69/0.88      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X2 @ X3)
% 0.69/0.88          | (r2_hidden @ X2 @ X4)
% 0.69/0.88          | ~ (r1_tarski @ X3 @ X4))),
% 0.69/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.88  thf('15', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         ((r2_hidden @ X0 @ sk_C_1)
% 0.69/0.88          | ~ (r2_hidden @ X0 @ 
% 0.69/0.88               (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['13', '14'])).
% 0.69/0.88  thf('16', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.69/0.88          | (r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ sk_C_1))),
% 0.69/0.88      inference('sup-', [status(thm)], ['12', '15'])).
% 0.69/0.88  thf('17', plain,
% 0.69/0.88      (![X3 : $i, X5 : $i]:
% 0.69/0.88         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.69/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.88  thf('18', plain,
% 0.69/0.88      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.69/0.88        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.69/0.88      inference('sup-', [status(thm)], ['16', '17'])).
% 0.69/0.88  thf('19', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.69/0.88      inference('simplify', [status(thm)], ['18'])).
% 0.69/0.88  thf('20', plain,
% 0.69/0.88      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X2 @ X3)
% 0.69/0.88          | (r2_hidden @ X2 @ X4)
% 0.69/0.88          | ~ (r1_tarski @ X3 @ X4))),
% 0.69/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.88  thf('21', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         ((r2_hidden @ X0 @ sk_C_1)
% 0.69/0.88          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['19', '20'])).
% 0.69/0.88  thf('22', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.69/0.88      inference('sup-', [status(thm)], ['7', '21'])).
% 0.69/0.88  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.69/0.88  
% 0.69/0.88  % SZS output end Refutation
% 0.69/0.88  
% 0.69/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
