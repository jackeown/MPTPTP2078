%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yllm2bhfCq

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 113 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  388 ( 948 expanded)
%              Number of equality atoms :   38 (  89 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t27_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( ( k2_tarski @ A @ B )
        = ( k1_tarski @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( ( k2_tarski @ A @ B )
          = ( k1_tarski @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_zfmisc_1])).

thf('0',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C_1 ) ),
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

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
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

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
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
    ~ ( zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_C_1 )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    sk_A = sk_C_1 ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','21'])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X6 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('29',plain,(
    sk_A = sk_C_1 ),
    inference(simplify,[status(thm)],['20'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('33',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['22','35','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yllm2bhfCq
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.19/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.55  % Solved by: fo/fo7.sh
% 0.19/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.55  % done 175 iterations in 0.101s
% 0.19/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.55  % SZS output start Refutation
% 0.19/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.19/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.55  thf(t27_zfmisc_1, conjecture,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.19/0.55       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.55        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.19/0.55          ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t27_zfmisc_1])).
% 0.19/0.55  thf('0', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C_1))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(d1_enumset1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.19/0.55       ( ![E:$i]:
% 0.19/0.55         ( ( r2_hidden @ E @ D ) <=>
% 0.19/0.55           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.19/0.55  thf(zf_stmt_1, axiom,
% 0.19/0.55    (![E:$i,C:$i,B:$i,A:$i]:
% 0.19/0.55     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.19/0.55       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.19/0.55  thf('1', plain,
% 0.19/0.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.55         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.19/0.55          | ((X5) = (X6))
% 0.19/0.55          | ((X5) = (X7))
% 0.19/0.55          | ((X5) = (X8)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.55  thf(t70_enumset1, axiom,
% 0.19/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.55  thf('2', plain,
% 0.19/0.55      (![X17 : $i, X18 : $i]:
% 0.19/0.55         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.19/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.55  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.19/0.55  thf(zf_stmt_3, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.19/0.55       ( ![E:$i]:
% 0.19/0.55         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.19/0.55  thf('3', plain,
% 0.19/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.55         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.19/0.55          | (r2_hidden @ X9 @ X13)
% 0.19/0.55          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.55  thf('4', plain,
% 0.19/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.55         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.19/0.55          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.19/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.55  thf('5', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.55          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.19/0.55      inference('sup+', [status(thm)], ['2', '4'])).
% 0.19/0.55  thf('6', plain,
% 0.19/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.55         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.55  thf('7', plain,
% 0.19/0.55      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.19/0.55      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.55  thf('8', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['5', '7'])).
% 0.19/0.55  thf('9', plain,
% 0.19/0.55      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(d3_tarski, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.55  thf('10', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.55          | (r2_hidden @ X0 @ X2)
% 0.19/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.55  thf('11', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((r2_hidden @ X0 @ (k1_tarski @ sk_C_1))
% 0.19/0.55          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.55  thf('12', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['8', '11'])).
% 0.19/0.55  thf(t69_enumset1, axiom,
% 0.19/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.55  thf('13', plain,
% 0.19/0.55      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.19/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.55  thf('14', plain,
% 0.19/0.55      (![X17 : $i, X18 : $i]:
% 0.19/0.55         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.19/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.55  thf('15', plain,
% 0.19/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X14 @ X13)
% 0.19/0.55          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.19/0.55          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.55  thf('16', plain,
% 0.19/0.55      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.19/0.55         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.19/0.55          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.55  thf('17', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.55          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['14', '16'])).
% 0.19/0.55  thf('18', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.19/0.55          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['13', '17'])).
% 0.19/0.55  thf('19', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_C_1 @ sk_C_1)),
% 0.19/0.55      inference('sup-', [status(thm)], ['12', '18'])).
% 0.19/0.55  thf('20', plain,
% 0.19/0.55      ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_C_1)) | ((sk_A) = (sk_C_1)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['1', '19'])).
% 0.19/0.55  thf('21', plain, (((sk_A) = (sk_C_1))),
% 0.19/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.55  thf('22', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['0', '21'])).
% 0.19/0.55  thf('23', plain,
% 0.19/0.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.55         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.19/0.55          | ((X5) = (X6))
% 0.19/0.55          | ((X5) = (X7))
% 0.19/0.55          | ((X5) = (X8)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.55  thf('24', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.55          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.19/0.55      inference('sup+', [status(thm)], ['2', '4'])).
% 0.19/0.55  thf('25', plain,
% 0.19/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.55         (((X5) != (X6)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.55  thf('26', plain,
% 0.19/0.55      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X6 @ X6 @ X7 @ X4)),
% 0.19/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.19/0.55  thf('27', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['24', '26'])).
% 0.19/0.55  thf('28', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((r2_hidden @ X0 @ (k1_tarski @ sk_C_1))
% 0.19/0.55          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.55  thf('29', plain, (((sk_A) = (sk_C_1))),
% 0.19/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.55  thf('30', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.19/0.55          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.55  thf('31', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['27', '30'])).
% 0.19/0.55  thf('32', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.19/0.55          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['13', '17'])).
% 0.19/0.55  thf('33', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 0.19/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.55  thf('34', plain,
% 0.19/0.55      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['23', '33'])).
% 0.19/0.55  thf('35', plain, (((sk_B) = (sk_A))),
% 0.19/0.55      inference('simplify', [status(thm)], ['34'])).
% 0.19/0.55  thf('36', plain,
% 0.19/0.55      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.19/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.55  thf('37', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['22', '35', '36'])).
% 0.19/0.55  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.19/0.55  
% 0.19/0.55  % SZS output end Refutation
% 0.19/0.55  
% 0.19/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
