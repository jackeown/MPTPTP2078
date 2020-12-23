%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WqRTYId0Fw

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 (  92 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :   20
%              Number of atoms          :  466 ( 749 expanded)
%              Number of equality atoms :   43 (  71 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('0',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
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

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k1_tarski @ sk_A ) )
        = sk_B )
      | ( ( sk_C @ X0 @ ( k1_tarski @ sk_A ) )
        = sk_B )
      | ( ( sk_C @ X0 @ ( k1_tarski @ sk_A ) )
        = sk_B )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_tarski @ sk_A ) )
        = sk_B ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_B = sk_A )
      | ( sk_B = sk_A )
      | ( sk_B = sk_A )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( sk_B = sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['10','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ( sk_A = X0 )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['1','40'])).

thf('42',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WqRTYId0Fw
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:05:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 100 iterations in 0.062s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.50  thf(t6_zfmisc_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.19/0.50       ( ( A ) = ( B ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i]:
% 0.19/0.50        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.19/0.50          ( ( A ) = ( B ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.19/0.50  thf('0', plain, (((sk_A) != (sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d1_enumset1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.19/0.50       ( ![E:$i]:
% 0.19/0.50         ( ( r2_hidden @ E @ D ) <=>
% 0.19/0.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_1, axiom,
% 0.19/0.50    (![E:$i,C:$i,B:$i,A:$i]:
% 0.19/0.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.19/0.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.50         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.19/0.50          | ((X5) = (X6))
% 0.19/0.50          | ((X5) = (X7))
% 0.19/0.50          | ((X5) = (X8)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.50  thf(t69_enumset1, axiom,
% 0.19/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.50  thf('2', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.50  thf(t70_enumset1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X17 : $i, X18 : $i]:
% 0.19/0.50         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.19/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.50  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.19/0.50  thf(zf_stmt_3, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.19/0.50       ( ![E:$i]:
% 0.19/0.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.50         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.19/0.50          | (r2_hidden @ X9 @ X13)
% 0.19/0.50          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.50         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.19/0.50          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.19/0.50      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.50          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.19/0.50      inference('sup+', [status(thm)], ['3', '5'])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.50         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.19/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '8'])).
% 0.19/0.50  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['2', '9'])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.50         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.19/0.50          | ((X5) = (X6))
% 0.19/0.50          | ((X5) = (X7))
% 0.19/0.50          | ((X5) = (X8)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.50         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.19/0.50          | ((X5) = (X6))
% 0.19/0.50          | ((X5) = (X7))
% 0.19/0.50          | ((X5) = (X8)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.50  thf(d3_tarski, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (![X1 : $i, X3 : $i]:
% 0.19/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('14', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.50          | (r2_hidden @ X0 @ X2)
% 0.19/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.19/0.50          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ (k1_tarski @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['13', '16'])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X17 : $i, X18 : $i]:
% 0.19/0.50         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.19/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X14 @ X13)
% 0.19/0.50          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.19/0.50          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.19/0.50         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.19/0.50          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.50          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['19', '21'])).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.19/0.50          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['18', '22'])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.19/0.50          | ~ (zip_tseitin_0 @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ sk_B @ 
% 0.19/0.50               sk_B @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['17', '23'])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((sk_C @ X0 @ (k1_tarski @ sk_A)) = (sk_B))
% 0.19/0.50          | ((sk_C @ X0 @ (k1_tarski @ sk_A)) = (sk_B))
% 0.19/0.50          | ((sk_C @ X0 @ (k1_tarski @ sk_A)) = (sk_B))
% 0.19/0.50          | (r1_tarski @ (k1_tarski @ sk_A) @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['12', '24'])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.19/0.50          | ((sk_C @ X0 @ (k1_tarski @ sk_A)) = (sk_B)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['25'])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X1 : $i, X3 : $i]:
% 0.19/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.19/0.50          | (r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.19/0.50          | (r1_tarski @ (k1_tarski @ sk_A) @ X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['26', '27'])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.19/0.50          | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.19/0.50          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['18', '22'])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.19/0.50          | ~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((sk_B) = (sk_A))
% 0.19/0.50          | ((sk_B) = (sk_A))
% 0.19/0.50          | ((sk_B) = (sk_A))
% 0.19/0.50          | (r1_tarski @ (k1_tarski @ sk_A) @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '31'])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      (![X0 : $i]: ((r1_tarski @ (k1_tarski @ sk_A) @ X0) | ((sk_B) = (sk_A)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['32'])).
% 0.19/0.50  thf('34', plain, (((sk_A) != (sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('35', plain, (![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ X0)),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.50          | (r2_hidden @ X0 @ X2)
% 0.19/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.50  thf('38', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.19/0.50      inference('sup-', [status(thm)], ['10', '37'])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.19/0.50          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['18', '22'])).
% 0.19/0.50  thf('40', plain, (![X0 : $i]: ~ (zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0)),
% 0.19/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      (![X0 : $i]: (((sk_A) = (X0)) | ((sk_A) = (X0)) | ((sk_A) = (X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '40'])).
% 0.19/0.50  thf('42', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['41'])).
% 0.19/0.50  thf('43', plain, (((sk_A) != (sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['0', '42'])).
% 0.19/0.50  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
