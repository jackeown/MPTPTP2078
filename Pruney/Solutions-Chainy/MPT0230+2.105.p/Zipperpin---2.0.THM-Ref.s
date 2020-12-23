%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IhRPsPDoju

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:22 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   42 (  49 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  277 ( 361 expanded)
%              Number of equality atoms :   30 (  43 expanded)
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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

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
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','12'])).

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
    inference(cnf,[status(esa)],[zf_stmt_2])).

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
    ~ ( zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IhRPsPDoju
% 0.17/0.37  % Computer   : n018.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 18:21:27 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.25/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.51  % Solved by: fo/fo7.sh
% 0.25/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.51  % done 39 iterations in 0.025s
% 0.25/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.51  % SZS output start Refutation
% 0.25/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.25/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.25/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.25/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.25/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.51  thf(d1_enumset1, axiom,
% 0.25/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.25/0.51       ( ![E:$i]:
% 0.25/0.51         ( ( r2_hidden @ E @ D ) <=>
% 0.25/0.51           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.25/0.51  thf(zf_stmt_0, axiom,
% 0.25/0.51    (![E:$i,C:$i,B:$i,A:$i]:
% 0.25/0.51     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.25/0.51       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.25/0.51  thf('0', plain,
% 0.25/0.51      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.25/0.51         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.25/0.51          | ((X5) = (X6))
% 0.25/0.51          | ((X5) = (X7))
% 0.25/0.51          | ((X5) = (X8)))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(t69_enumset1, axiom,
% 0.25/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.25/0.51  thf('1', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.25/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.25/0.51  thf(t70_enumset1, axiom,
% 0.25/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.25/0.51  thf('2', plain,
% 0.25/0.51      (![X17 : $i, X18 : $i]:
% 0.25/0.51         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.25/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.25/0.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.25/0.51  thf(zf_stmt_2, axiom,
% 0.25/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.25/0.51       ( ![E:$i]:
% 0.25/0.51         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.25/0.51  thf('3', plain,
% 0.25/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.25/0.51         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.25/0.51          | (r2_hidden @ X9 @ X13)
% 0.25/0.51          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.25/0.51  thf('4', plain,
% 0.25/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.25/0.51         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.25/0.51          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.25/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.25/0.51  thf('5', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.51         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.25/0.51          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.25/0.51      inference('sup+', [status(thm)], ['2', '4'])).
% 0.25/0.51  thf('6', plain,
% 0.25/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.25/0.51         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('7', plain,
% 0.25/0.51      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.25/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.25/0.51  thf('8', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.25/0.51      inference('sup-', [status(thm)], ['5', '7'])).
% 0.25/0.51  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.25/0.51      inference('sup+', [status(thm)], ['1', '8'])).
% 0.25/0.51  thf(t25_zfmisc_1, conjecture,
% 0.25/0.51    (![A:$i,B:$i,C:$i]:
% 0.25/0.51     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.25/0.51          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.25/0.51  thf(zf_stmt_3, negated_conjecture,
% 0.25/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.25/0.51        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.25/0.51             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.25/0.51    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.25/0.51  thf('10', plain,
% 0.25/0.51      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.25/0.51  thf(d3_tarski, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.25/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.25/0.51  thf('11', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.25/0.51          | (r2_hidden @ X0 @ X2)
% 0.25/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.25/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.51  thf('12', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C_1))
% 0.25/0.51          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.25/0.51  thf('13', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C_1))),
% 0.25/0.51      inference('sup-', [status(thm)], ['9', '12'])).
% 0.25/0.51  thf('14', plain,
% 0.25/0.51      (![X17 : $i, X18 : $i]:
% 0.25/0.51         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.25/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.25/0.51  thf('15', plain,
% 0.25/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X14 @ X13)
% 0.25/0.51          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.25/0.51          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.25/0.51  thf('16', plain,
% 0.25/0.51      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.25/0.51         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.25/0.51          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.25/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.25/0.51  thf('17', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.25/0.51          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.25/0.51      inference('sup-', [status(thm)], ['14', '16'])).
% 0.25/0.51  thf('18', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_B @ sk_B)),
% 0.25/0.51      inference('sup-', [status(thm)], ['13', '17'])).
% 0.25/0.51  thf('19', plain,
% 0.25/0.51      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_C_1)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['0', '18'])).
% 0.25/0.51  thf('20', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_B)))),
% 0.25/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.25/0.51  thf('21', plain, (((sk_A) != (sk_B))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.25/0.51  thf('22', plain, (((sk_A) != (sk_C_1))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.25/0.51  thf('23', plain, ($false),
% 0.25/0.51      inference('simplify_reflect-', [status(thm)], ['20', '21', '22'])).
% 0.25/0.51  
% 0.25/0.51  % SZS output end Refutation
% 0.25/0.51  
% 0.25/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
