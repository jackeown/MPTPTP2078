%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VBKzFernjl

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:26 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   51 (  70 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  319 ( 515 expanded)
%              Number of equality atoms :   20 (  36 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X12 @ X16 )
      | ( X16
       != ( k1_enumset1 @ X15 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k1_enumset1 @ X15 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X7 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X9 @ X10 @ X7 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
    | ( sk_C_1
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X9 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X9 @ X10 @ X7 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('15',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ ( k3_tarski @ X50 ) )
      | ~ ( r2_hidden @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_C_1
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('21',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ ( k3_tarski @ X50 ) )
      | ~ ( r2_hidden @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference('sup+',[status(thm)],['19','24'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VBKzFernjl
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:04:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.77/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.99  % Solved by: fo/fo7.sh
% 0.77/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.99  % done 270 iterations in 0.522s
% 0.77/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.99  % SZS output start Refutation
% 0.77/0.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.77/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.99  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.77/0.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.77/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.77/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.99  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.77/0.99  thf(t47_zfmisc_1, conjecture,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.77/0.99       ( r2_hidden @ A @ C ) ))).
% 0.77/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.99    (~( ![A:$i,B:$i,C:$i]:
% 0.77/0.99        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.77/0.99          ( r2_hidden @ A @ C ) ) )),
% 0.77/0.99    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.77/0.99  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(t70_enumset1, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.77/0.99  thf('1', plain,
% 0.77/0.99      (![X22 : $i, X23 : $i]:
% 0.77/0.99         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.77/0.99      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.77/0.99  thf(d1_enumset1, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.99     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.77/0.99       ( ![E:$i]:
% 0.77/0.99         ( ( r2_hidden @ E @ D ) <=>
% 0.77/0.99           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.77/0.99  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.77/0.99  thf(zf_stmt_2, axiom,
% 0.77/0.99    (![E:$i,C:$i,B:$i,A:$i]:
% 0.77/0.99     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.77/0.99       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.77/0.99  thf(zf_stmt_3, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.99     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.77/0.99       ( ![E:$i]:
% 0.77/0.99         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.77/0.99  thf('2', plain,
% 0.77/0.99      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.77/0.99         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.77/0.99          | (r2_hidden @ X12 @ X16)
% 0.77/0.99          | ((X16) != (k1_enumset1 @ X15 @ X14 @ X13)))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.77/0.99  thf('3', plain,
% 0.77/0.99      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.77/0.99         ((r2_hidden @ X12 @ (k1_enumset1 @ X15 @ X14 @ X13))
% 0.77/0.99          | (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 0.77/0.99      inference('simplify', [status(thm)], ['2'])).
% 0.77/0.99  thf('4', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.99         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.77/0.99          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['1', '3'])).
% 0.77/0.99  thf('5', plain,
% 0.77/0.99      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.77/0.99         (((X8) != (X7)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.77/0.99  thf('6', plain,
% 0.77/0.99      (![X7 : $i, X9 : $i, X10 : $i]: ~ (zip_tseitin_0 @ X7 @ X9 @ X10 @ X7)),
% 0.77/0.99      inference('simplify', [status(thm)], ['5'])).
% 0.77/0.99  thf('7', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.77/0.99      inference('sup-', [status(thm)], ['4', '6'])).
% 0.77/0.99  thf('8', plain,
% 0.77/0.99      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) @ sk_C_1)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(d10_xboole_0, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/0.99  thf('9', plain,
% 0.77/0.99      (![X4 : $i, X6 : $i]:
% 0.77/0.99         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.77/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/0.99  thf('10', plain,
% 0.77/0.99      ((~ (r1_tarski @ sk_C_1 @ 
% 0.77/0.99           (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.77/0.99        | ((sk_C_1) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['8', '9'])).
% 0.77/0.99  thf('11', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.99         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.77/0.99          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['1', '3'])).
% 0.77/0.99  thf('12', plain,
% 0.77/0.99      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.77/0.99         (((X8) != (X9)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.77/0.99  thf('13', plain,
% 0.77/0.99      (![X7 : $i, X9 : $i, X10 : $i]: ~ (zip_tseitin_0 @ X9 @ X9 @ X10 @ X7)),
% 0.77/0.99      inference('simplify', [status(thm)], ['12'])).
% 0.77/0.99  thf('14', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.77/0.99      inference('sup-', [status(thm)], ['11', '13'])).
% 0.77/0.99  thf(l49_zfmisc_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.77/0.99  thf('15', plain,
% 0.77/0.99      (![X49 : $i, X50 : $i]:
% 0.77/0.99         ((r1_tarski @ X49 @ (k3_tarski @ X50)) | ~ (r2_hidden @ X49 @ X50))),
% 0.77/0.99      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.77/0.99  thf('16', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['14', '15'])).
% 0.77/0.99  thf(l51_zfmisc_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.99  thf('17', plain,
% 0.77/0.99      (![X51 : $i, X52 : $i]:
% 0.77/0.99         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.77/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/0.99  thf('18', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.77/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.77/0.99  thf('19', plain,
% 0.77/0.99      (((sk_C_1) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.77/0.99      inference('demod', [status(thm)], ['10', '18'])).
% 0.77/0.99  thf('20', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.77/0.99      inference('sup-', [status(thm)], ['4', '6'])).
% 0.77/0.99  thf('21', plain,
% 0.77/0.99      (![X49 : $i, X50 : $i]:
% 0.77/0.99         ((r1_tarski @ X49 @ (k3_tarski @ X50)) | ~ (r2_hidden @ X49 @ X50))),
% 0.77/0.99      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.77/0.99  thf('22', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         (r1_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['20', '21'])).
% 0.77/0.99  thf('23', plain,
% 0.77/0.99      (![X51 : $i, X52 : $i]:
% 0.77/0.99         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.77/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/0.99  thf('24', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.77/0.99      inference('demod', [status(thm)], ['22', '23'])).
% 0.77/0.99  thf('25', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.77/0.99      inference('sup+', [status(thm)], ['19', '24'])).
% 0.77/0.99  thf(d3_tarski, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( r1_tarski @ A @ B ) <=>
% 0.77/0.99       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.77/0.99  thf('26', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.99         (~ (r2_hidden @ X0 @ X1)
% 0.77/0.99          | (r2_hidden @ X0 @ X2)
% 0.77/0.99          | ~ (r1_tarski @ X1 @ X2))),
% 0.77/0.99      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.99  thf('27', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((r2_hidden @ X0 @ sk_C_1)
% 0.77/0.99          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['25', '26'])).
% 0.77/0.99  thf('28', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.77/0.99      inference('sup-', [status(thm)], ['7', '27'])).
% 0.77/0.99  thf('29', plain, ($false), inference('demod', [status(thm)], ['0', '28'])).
% 0.77/0.99  
% 0.77/0.99  % SZS output end Refutation
% 0.77/0.99  
% 0.77/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
