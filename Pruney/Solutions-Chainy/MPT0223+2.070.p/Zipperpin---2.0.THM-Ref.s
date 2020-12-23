%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qZYWXIOsPm

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:39 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   65 (  96 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  499 ( 797 expanded)
%              Number of equality atoms :   43 (  74 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_hidden @ X11 @ X15 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X8 @ X9 @ X6 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ X3 ) )
      | ( r2_hidden @ X0 @ X3 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X18 @ X19 @ X20 ) @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('30',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['19','28','29'])).

thf('31',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','37'])).

thf('39',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qZYWXIOsPm
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.61  % Solved by: fo/fo7.sh
% 0.46/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.61  % done 152 iterations in 0.162s
% 0.46/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.61  % SZS output start Refutation
% 0.46/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.46/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.46/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.61  thf(d1_enumset1, axiom,
% 0.46/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.61       ( ![E:$i]:
% 0.46/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.46/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.46/0.61  thf(zf_stmt_0, axiom,
% 0.46/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.46/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.46/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.46/0.61  thf('0', plain,
% 0.46/0.61      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.61         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.46/0.61          | ((X7) = (X8))
% 0.46/0.61          | ((X7) = (X9))
% 0.46/0.61          | ((X7) = (X10)))),
% 0.46/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.61  thf(t69_enumset1, axiom,
% 0.46/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.61  thf('1', plain, (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.46/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.61  thf(t70_enumset1, axiom,
% 0.46/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.61  thf('2', plain,
% 0.46/0.61      (![X23 : $i, X24 : $i]:
% 0.46/0.61         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.46/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.61  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.46/0.61  thf(zf_stmt_2, axiom,
% 0.46/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.61       ( ![E:$i]:
% 0.46/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.46/0.61  thf('3', plain,
% 0.46/0.61      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.61         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.46/0.61          | (r2_hidden @ X11 @ X15)
% 0.46/0.61          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.46/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.61  thf('4', plain,
% 0.46/0.61      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.61         ((r2_hidden @ X11 @ (k1_enumset1 @ X14 @ X13 @ X12))
% 0.46/0.61          | (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14))),
% 0.46/0.61      inference('simplify', [status(thm)], ['3'])).
% 0.46/0.61  thf('5', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.61         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.61          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.46/0.61      inference('sup+', [status(thm)], ['2', '4'])).
% 0.46/0.61  thf('6', plain,
% 0.46/0.61      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.61         (((X7) != (X6)) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.46/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.61  thf('7', plain,
% 0.46/0.61      (![X6 : $i, X8 : $i, X9 : $i]: ~ (zip_tseitin_0 @ X6 @ X8 @ X9 @ X6)),
% 0.46/0.61      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.61  thf('8', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.46/0.61      inference('sup-', [status(thm)], ['5', '7'])).
% 0.46/0.61  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.61      inference('sup+', [status(thm)], ['1', '8'])).
% 0.46/0.61  thf(t1_xboole_0, axiom,
% 0.46/0.61    (![A:$i,B:$i,C:$i]:
% 0.46/0.61     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.46/0.61       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.46/0.61  thf('10', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.46/0.61         ((r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ X3))
% 0.46/0.61          | (r2_hidden @ X0 @ X3)
% 0.46/0.61          | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.61      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.46/0.61  thf('11', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i]:
% 0.46/0.61         ((r2_hidden @ X0 @ X1)
% 0.46/0.61          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.46/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.61  thf(t18_zfmisc_1, conjecture,
% 0.46/0.61    (![A:$i,B:$i]:
% 0.46/0.61     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.46/0.61         ( k1_tarski @ A ) ) =>
% 0.46/0.61       ( ( A ) = ( B ) ) ))).
% 0.46/0.61  thf(zf_stmt_3, negated_conjecture,
% 0.46/0.61    (~( ![A:$i,B:$i]:
% 0.46/0.61        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.46/0.61            ( k1_tarski @ A ) ) =>
% 0.46/0.61          ( ( A ) = ( B ) ) ) )),
% 0.46/0.61    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.46/0.61  thf('12', plain,
% 0.46/0.61      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.46/0.61         = (k1_tarski @ sk_A))),
% 0.46/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.61  thf(t95_xboole_1, axiom,
% 0.46/0.61    (![A:$i,B:$i]:
% 0.46/0.61     ( ( k3_xboole_0 @ A @ B ) =
% 0.46/0.61       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.46/0.61  thf('13', plain,
% 0.46/0.61      (![X4 : $i, X5 : $i]:
% 0.46/0.61         ((k3_xboole_0 @ X4 @ X5)
% 0.46/0.61           = (k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ (k2_xboole_0 @ X4 @ X5)))),
% 0.46/0.61      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.46/0.61  thf('14', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.61          | ~ (r2_hidden @ X0 @ X2)
% 0.46/0.61          | ~ (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.46/0.61      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.46/0.61  thf('15', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.61         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.61          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.46/0.61          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.61  thf('16', plain,
% 0.46/0.61      (![X0 : $i]:
% 0.46/0.61         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.46/0.61          | ~ (r2_hidden @ X0 @ 
% 0.46/0.61               (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.46/0.61          | ~ (r2_hidden @ X0 @ 
% 0.46/0.61               (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 0.46/0.61      inference('sup-', [status(thm)], ['12', '15'])).
% 0.46/0.61  thf('17', plain,
% 0.46/0.61      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B))
% 0.46/0.61        | ~ (r2_hidden @ sk_A @ 
% 0.46/0.61             (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.46/0.61        | ~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.46/0.61      inference('sup-', [status(thm)], ['11', '16'])).
% 0.46/0.61  thf('18', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.61      inference('sup+', [status(thm)], ['1', '8'])).
% 0.46/0.61  thf('19', plain,
% 0.46/0.61      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B))
% 0.46/0.61        | ~ (r2_hidden @ sk_A @ 
% 0.46/0.61             (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 0.46/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.46/0.61  thf('20', plain,
% 0.46/0.61      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.46/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.61  thf('21', plain,
% 0.46/0.61      (![X23 : $i, X24 : $i]:
% 0.46/0.61         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.46/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.61  thf(t46_enumset1, axiom,
% 0.46/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.61     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.46/0.61       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.46/0.61  thf('22', plain,
% 0.46/0.61      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.61         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 0.46/0.61           = (k2_xboole_0 @ (k1_enumset1 @ X18 @ X19 @ X20) @ (k1_tarski @ X21)))),
% 0.46/0.61      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.46/0.61  thf('23', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.61         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.46/0.61           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.46/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.46/0.61  thf('24', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i]:
% 0.46/0.61         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.46/0.61           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.46/0.61      inference('sup+', [status(thm)], ['20', '23'])).
% 0.46/0.61  thf(t71_enumset1, axiom,
% 0.46/0.61    (![A:$i,B:$i,C:$i]:
% 0.46/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.46/0.61  thf('25', plain,
% 0.46/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.61         ((k2_enumset1 @ X25 @ X25 @ X26 @ X27)
% 0.46/0.61           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 0.46/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.46/0.61  thf('26', plain,
% 0.46/0.61      (![X23 : $i, X24 : $i]:
% 0.46/0.61         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.46/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.61  thf('27', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i]:
% 0.46/0.61         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.46/0.61      inference('sup+', [status(thm)], ['25', '26'])).
% 0.46/0.61  thf('28', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i]:
% 0.46/0.61         ((k2_tarski @ X0 @ X1)
% 0.46/0.61           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.46/0.61      inference('demod', [status(thm)], ['24', '27'])).
% 0.46/0.61  thf('29', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.46/0.61      inference('sup-', [status(thm)], ['5', '7'])).
% 0.46/0.61  thf('30', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.46/0.61      inference('demod', [status(thm)], ['19', '28', '29'])).
% 0.46/0.61  thf('31', plain,
% 0.46/0.61      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.46/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.61  thf('32', plain,
% 0.46/0.61      (![X23 : $i, X24 : $i]:
% 0.46/0.61         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.46/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.61  thf('33', plain,
% 0.46/0.61      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.61         (~ (r2_hidden @ X16 @ X15)
% 0.46/0.61          | ~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.46/0.61          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.46/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.61  thf('34', plain,
% 0.46/0.61      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.46/0.61         (~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.46/0.61          | ~ (r2_hidden @ X16 @ (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.46/0.61      inference('simplify', [status(thm)], ['33'])).
% 0.46/0.61  thf('35', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.61         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.61          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.46/0.61      inference('sup-', [status(thm)], ['32', '34'])).
% 0.46/0.61  thf('36', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i]:
% 0.46/0.61         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.46/0.61          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.46/0.61      inference('sup-', [status(thm)], ['31', '35'])).
% 0.46/0.61  thf('37', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.46/0.61      inference('sup-', [status(thm)], ['30', '36'])).
% 0.46/0.61  thf('38', plain,
% 0.46/0.61      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.46/0.61      inference('sup-', [status(thm)], ['0', '37'])).
% 0.46/0.61  thf('39', plain, (((sk_A) = (sk_B))),
% 0.46/0.61      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.61  thf('40', plain, (((sk_A) != (sk_B))),
% 0.46/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.61  thf('41', plain, ($false),
% 0.46/0.61      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.46/0.61  
% 0.46/0.61  % SZS output end Refutation
% 0.46/0.61  
% 0.46/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
