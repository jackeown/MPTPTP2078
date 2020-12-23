%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P8pPqovrP4

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  368 ( 439 expanded)
%              Number of equality atoms :   39 (  49 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X6 )
      | ( X3 = X4 )
      | ( X3 = X5 )
      | ( X3 = X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t87_enumset1,axiom,(
    ! [A: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X28: $i] :
      ( ( k3_enumset1 @ X28 @ X28 @ X28 @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t87_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t84_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_enumset1 @ X25 @ X25 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t84_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['1','6'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X7 @ X11 )
      | ( X11
       != ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k1_enumset1 @ X10 @ X9 @ X8 ) )
      | ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3 != X4 )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X4 @ X5 @ X2 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X28: $i] :
      ( ( k3_enumset1 @ X28 @ X28 @ X28 @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t87_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k4_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_enumset1 @ X25 @ X25 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t84_enumset1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X8 @ X9 @ X10 )
      | ( X11
       != ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X8 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','22'])).

thf('24',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P8pPqovrP4
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 57 iterations in 0.035s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.49  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(d1_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.49       ( ![E:$i]:
% 0.20/0.49         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.49           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, axiom,
% 0.20/0.49    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.49       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         ((zip_tseitin_0 @ X3 @ X4 @ X5 @ X6)
% 0.20/0.49          | ((X3) = (X4))
% 0.20/0.49          | ((X3) = (X5))
% 0.20/0.49          | ((X3) = (X6)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t13_zfmisc_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.49         ( k1_tarski @ A ) ) =>
% 0.20/0.49       ( ( A ) = ( B ) ) ))).
% 0.20/0.49  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.49            ( k1_tarski @ A ) ) =>
% 0.20/0.49          ( ( A ) = ( B ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.49         = (k1_tarski @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.49  thf(t87_enumset1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_enumset1 @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X28 : $i]:
% 0.20/0.49         ((k3_enumset1 @ X28 @ X28 @ X28 @ X28 @ X28) = (k1_tarski @ X28))),
% 0.20/0.49      inference('cnf', [status(esa)], [t87_enumset1])).
% 0.20/0.49  thf(t55_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.49     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.49       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.49         ((k4_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.20/0.49           = (k2_xboole_0 @ (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18) @ 
% 0.20/0.49              (k1_tarski @ X19)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1)
% 0.20/0.49           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf(t84_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.49         ((k4_enumset1 @ X25 @ X25 @ X25 @ X25 @ X26 @ X27)
% 0.20/0.49           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 0.20/0.49      inference('cnf', [status(esa)], [t84_enumset1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.20/0.49           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain, (((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['1', '6'])).
% 0.20/0.49  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_3, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.49       ( ![E:$i]:
% 0.20/0.49         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.49         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.20/0.49          | (r2_hidden @ X7 @ X11)
% 0.20/0.49          | ((X11) != (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.49         ((r2_hidden @ X7 @ (k1_enumset1 @ X10 @ X9 @ X8))
% 0.20/0.49          | (zip_tseitin_0 @ X7 @ X8 @ X9 @ X10))),
% 0.20/0.49      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.49          | (zip_tseitin_0 @ X0 @ sk_B @ sk_A @ sk_A))),
% 0.20/0.49      inference('sup+', [status(thm)], ['7', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         (((X3) != (X4)) | ~ (zip_tseitin_0 @ X3 @ X4 @ X5 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X2 : $i, X4 : $i, X5 : $i]: ~ (zip_tseitin_0 @ X4 @ X4 @ X5 @ X2)),
% 0.20/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.49  thf('13', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X28 : $i]:
% 0.20/0.49         ((k3_enumset1 @ X28 @ X28 @ X28 @ X28 @ X28) = (k1_tarski @ X28))),
% 0.20/0.49      inference('cnf', [status(esa)], [t87_enumset1])).
% 0.20/0.49  thf(t73_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.49     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.20/0.49       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.49         ((k4_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.20/0.49           = (k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24))),
% 0.20/0.49      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.49         ((k4_enumset1 @ X25 @ X25 @ X25 @ X25 @ X26 @ X27)
% 0.20/0.49           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 0.20/0.49      inference('cnf', [status(esa)], [t84_enumset1])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X12 @ X11)
% 0.20/0.49          | ~ (zip_tseitin_0 @ X12 @ X8 @ X9 @ X10)
% 0.20/0.49          | ((X11) != (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.20/0.49         (~ (zip_tseitin_0 @ X12 @ X8 @ X9 @ X10)
% 0.20/0.49          | ~ (r2_hidden @ X12 @ (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.49          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '20'])).
% 0.20/0.49  thf('22', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '22'])).
% 0.20/0.49  thf('24', plain, (((sk_B) = (sk_A))),
% 0.20/0.49      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.49  thf('25', plain, (((sk_A) != (sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.49  thf('26', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
