%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6NeU72n7P0

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:20 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X45: $i,X46: $i] :
      ( ( k1_enumset1 @ X45 @ X45 @ X46 )
      = ( k2_tarski @ X45 @ X46 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 )
      | ( r2_hidden @ X27 @ X31 )
      | ( X31
       != ( k1_enumset1 @ X30 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X27 @ ( k1_enumset1 @ X30 @ X29 @ X28 ) )
      | ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X22 ) ),
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
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
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
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6NeU72n7P0
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:44:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.36/1.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.36/1.62  % Solved by: fo/fo7.sh
% 1.36/1.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.62  % done 1159 iterations in 1.160s
% 1.36/1.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.36/1.62  % SZS output start Refutation
% 1.36/1.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.36/1.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.36/1.62  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.36/1.62  thf(sk_B_type, type, sk_B: $i).
% 1.36/1.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.36/1.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.36/1.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.36/1.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.36/1.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.36/1.62  thf(t47_zfmisc_1, conjecture,
% 1.36/1.62    (![A:$i,B:$i,C:$i]:
% 1.36/1.62     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 1.36/1.62       ( r2_hidden @ A @ C ) ))).
% 1.36/1.62  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.62    (~( ![A:$i,B:$i,C:$i]:
% 1.36/1.62        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 1.36/1.62          ( r2_hidden @ A @ C ) ) )),
% 1.36/1.62    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 1.36/1.62  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.62  thf(t70_enumset1, axiom,
% 1.36/1.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.36/1.62  thf('1', plain,
% 1.36/1.62      (![X45 : $i, X46 : $i]:
% 1.36/1.62         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 1.36/1.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.36/1.62  thf(d1_enumset1, axiom,
% 1.36/1.62    (![A:$i,B:$i,C:$i,D:$i]:
% 1.36/1.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.36/1.62       ( ![E:$i]:
% 1.36/1.62         ( ( r2_hidden @ E @ D ) <=>
% 1.36/1.62           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.36/1.62  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.36/1.62  thf(zf_stmt_2, axiom,
% 1.36/1.62    (![E:$i,C:$i,B:$i,A:$i]:
% 1.36/1.62     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.36/1.62       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.36/1.62  thf(zf_stmt_3, axiom,
% 1.36/1.62    (![A:$i,B:$i,C:$i,D:$i]:
% 1.36/1.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.36/1.62       ( ![E:$i]:
% 1.36/1.62         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.36/1.62  thf('2', plain,
% 1.36/1.62      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.36/1.62         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30)
% 1.36/1.62          | (r2_hidden @ X27 @ X31)
% 1.36/1.62          | ((X31) != (k1_enumset1 @ X30 @ X29 @ X28)))),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.36/1.62  thf('3', plain,
% 1.36/1.62      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.36/1.62         ((r2_hidden @ X27 @ (k1_enumset1 @ X30 @ X29 @ X28))
% 1.36/1.62          | (zip_tseitin_0 @ X27 @ X28 @ X29 @ X30))),
% 1.36/1.62      inference('simplify', [status(thm)], ['2'])).
% 1.36/1.62  thf('4', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.62         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.36/1.62          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.36/1.62      inference('sup+', [status(thm)], ['1', '3'])).
% 1.36/1.62  thf('5', plain,
% 1.36/1.62      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.36/1.62         (((X23) != (X22)) | ~ (zip_tseitin_0 @ X23 @ X24 @ X25 @ X22))),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.36/1.62  thf('6', plain,
% 1.36/1.62      (![X22 : $i, X24 : $i, X25 : $i]:
% 1.36/1.62         ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X22)),
% 1.36/1.62      inference('simplify', [status(thm)], ['5'])).
% 1.36/1.62  thf('7', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.36/1.62      inference('sup-', [status(thm)], ['4', '6'])).
% 1.36/1.62  thf(d3_tarski, axiom,
% 1.36/1.62    (![A:$i,B:$i]:
% 1.36/1.62     ( ( r1_tarski @ A @ B ) <=>
% 1.36/1.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.36/1.62  thf('8', plain,
% 1.36/1.62      (![X3 : $i, X5 : $i]:
% 1.36/1.62         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.36/1.62      inference('cnf', [status(esa)], [d3_tarski])).
% 1.36/1.62  thf(t7_xboole_1, axiom,
% 1.36/1.62    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.36/1.62  thf('9', plain,
% 1.36/1.62      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 1.36/1.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.36/1.62  thf('10', plain,
% 1.36/1.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.36/1.62         (~ (r2_hidden @ X2 @ X3)
% 1.36/1.62          | (r2_hidden @ X2 @ X4)
% 1.36/1.62          | ~ (r1_tarski @ X3 @ X4))),
% 1.36/1.62      inference('cnf', [status(esa)], [d3_tarski])).
% 1.36/1.62  thf('11', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.62         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 1.36/1.62      inference('sup-', [status(thm)], ['9', '10'])).
% 1.36/1.62  thf('12', plain,
% 1.36/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.62         ((r1_tarski @ X0 @ X1)
% 1.36/1.62          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['8', '11'])).
% 1.36/1.62  thf('13', plain,
% 1.36/1.62      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) @ sk_C_1)),
% 1.36/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.62  thf('14', plain,
% 1.36/1.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.36/1.62         (~ (r2_hidden @ X2 @ X3)
% 1.36/1.62          | (r2_hidden @ X2 @ X4)
% 1.36/1.62          | ~ (r1_tarski @ X3 @ X4))),
% 1.36/1.62      inference('cnf', [status(esa)], [d3_tarski])).
% 1.36/1.62  thf('15', plain,
% 1.36/1.62      (![X0 : $i]:
% 1.36/1.62         ((r2_hidden @ X0 @ sk_C_1)
% 1.36/1.62          | ~ (r2_hidden @ X0 @ 
% 1.36/1.62               (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['13', '14'])).
% 1.36/1.62  thf('16', plain,
% 1.36/1.62      (![X0 : $i]:
% 1.36/1.62         ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 1.36/1.62          | (r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ sk_C_1))),
% 1.36/1.62      inference('sup-', [status(thm)], ['12', '15'])).
% 1.36/1.62  thf('17', plain,
% 1.36/1.62      (![X3 : $i, X5 : $i]:
% 1.36/1.62         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 1.36/1.62      inference('cnf', [status(esa)], [d3_tarski])).
% 1.36/1.62  thf('18', plain,
% 1.36/1.62      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.36/1.62        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 1.36/1.62      inference('sup-', [status(thm)], ['16', '17'])).
% 1.36/1.62  thf('19', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 1.36/1.62      inference('simplify', [status(thm)], ['18'])).
% 1.36/1.62  thf('20', plain,
% 1.36/1.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.36/1.62         (~ (r2_hidden @ X2 @ X3)
% 1.36/1.62          | (r2_hidden @ X2 @ X4)
% 1.36/1.62          | ~ (r1_tarski @ X3 @ X4))),
% 1.36/1.62      inference('cnf', [status(esa)], [d3_tarski])).
% 1.36/1.62  thf('21', plain,
% 1.36/1.62      (![X0 : $i]:
% 1.36/1.62         ((r2_hidden @ X0 @ sk_C_1)
% 1.36/1.62          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 1.36/1.62      inference('sup-', [status(thm)], ['19', '20'])).
% 1.36/1.62  thf('22', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 1.36/1.62      inference('sup-', [status(thm)], ['7', '21'])).
% 1.36/1.62  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 1.36/1.62  
% 1.36/1.62  % SZS output end Refutation
% 1.36/1.62  
% 1.44/1.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
