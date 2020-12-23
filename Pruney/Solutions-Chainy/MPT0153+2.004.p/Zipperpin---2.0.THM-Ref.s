%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DtNPOlBriv

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  40 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :   14
%              Number of atoms          :  306 ( 479 expanded)
%              Number of equality atoms :   50 (  81 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t69_enumset1,conjecture,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k2_tarski @ A @ A )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t69_enumset1])).

thf('0',plain,(
    ( k2_tarski @ sk_A @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ( X9 = X8 )
      | ( X9 = X5 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('3',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( X9 = X5 )
      | ( X9 = X8 )
      | ~ ( r2_hidden @ X9 @ ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X2 )
      | ( ( sk_C @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = X1 )
      | ( ( sk_C @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = X2 )
      | ( ( k2_tarski @ X2 @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X2 @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k2_tarski @ X2 @ X1 ) @ X2 )
        = X2 )
      | ( ( sk_C @ ( k2_tarski @ X2 @ X1 ) @ X2 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X1 ) @ X0 )
        = X1 )
      | ( ( k2_tarski @ X0 @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X1 ) @ X1 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X1 ) @ X1 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('10',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
       != X0 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X0 )
       != X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X5 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('13',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X5 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X0 )
       != X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X0 )
       != X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DtNPOlBriv
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:13:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 24 iterations in 0.016s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(t69_enumset1, conjecture,
% 0.21/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf('0', plain, (((k2_tarski @ sk_A @ sk_A) != (k1_tarski @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d1_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X0 : $i, X4 : $i]:
% 0.21/0.48         (((X4) = (k1_tarski @ X0))
% 0.21/0.48          | ((sk_C @ X4 @ X0) = (X0))
% 0.21/0.48          | (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.48  thf(d2_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X5 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X9 @ X7)
% 0.21/0.48          | ((X9) = (X8))
% 0.21/0.48          | ((X9) = (X5))
% 0.21/0.48          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X5 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X9) = (X5))
% 0.21/0.48          | ((X9) = (X8))
% 0.21/0.48          | ~ (r2_hidden @ X9 @ (k2_tarski @ X8 @ X5)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (((sk_C @ (k2_tarski @ X1 @ X0) @ X2) = (X2))
% 0.21/0.48          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X2))
% 0.21/0.48          | ((sk_C @ (k2_tarski @ X1 @ X0) @ X2) = (X1))
% 0.21/0.48          | ((sk_C @ (k2_tarski @ X1 @ X0) @ X2) = (X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (((X0) != (X2))
% 0.21/0.48          | ((sk_C @ (k2_tarski @ X2 @ X1) @ X0) = (X1))
% 0.21/0.48          | ((sk_C @ (k2_tarski @ X2 @ X1) @ X0) = (X2))
% 0.21/0.48          | ((k2_tarski @ X2 @ X1) = (k1_tarski @ X0)))),
% 0.21/0.48      inference('eq_fact', [status(thm)], ['4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         (((k2_tarski @ X2 @ X1) = (k1_tarski @ X2))
% 0.21/0.48          | ((sk_C @ (k2_tarski @ X2 @ X1) @ X2) = (X2))
% 0.21/0.48          | ((sk_C @ (k2_tarski @ X2 @ X1) @ X2) = (X1)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((X0) != (X1))
% 0.21/0.48          | ((sk_C @ (k2_tarski @ X0 @ X1) @ X0) = (X1))
% 0.21/0.48          | ((k2_tarski @ X0 @ X1) = (k1_tarski @ X0)))),
% 0.21/0.48      inference('eq_fact', [status(thm)], ['6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X1 : $i]:
% 0.21/0.48         (((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))
% 0.21/0.48          | ((sk_C @ (k2_tarski @ X1 @ X1) @ X1) = (X1)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X1 : $i]:
% 0.21/0.48         (((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))
% 0.21/0.48          | ((sk_C @ (k2_tarski @ X1 @ X1) @ X1) = (X1)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X4 : $i]:
% 0.21/0.48         (((X4) = (k1_tarski @ X0))
% 0.21/0.48          | ((sk_C @ X4 @ X0) != (X0))
% 0.21/0.48          | ~ (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))
% 0.21/0.48          | ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))
% 0.21/0.48          | ((sk_C @ (k2_tarski @ X0 @ X0) @ X0) != (X0))
% 0.21/0.48          | ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.48         (((X6) != (X5))
% 0.21/0.48          | (r2_hidden @ X6 @ X7)
% 0.21/0.48          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X5 : $i, X8 : $i]: (r2_hidden @ X5 @ (k2_tarski @ X8 @ X5))),
% 0.21/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))
% 0.21/0.48          | ((sk_C @ (k2_tarski @ X0 @ X0) @ X0) != (X0))
% 0.21/0.48          | ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((sk_C @ (k2_tarski @ X0 @ X0) @ X0) != (X0))
% 0.21/0.48          | ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((X0) != (X0))
% 0.21/0.48          | ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))
% 0.21/0.48          | ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '15'])).
% 0.21/0.48  thf('17', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.48  thf('18', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '17'])).
% 0.21/0.48  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
