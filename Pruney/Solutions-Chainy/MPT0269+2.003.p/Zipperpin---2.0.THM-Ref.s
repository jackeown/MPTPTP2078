%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JbEXP8DOu4

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:02 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  214 ( 301 expanded)
%              Number of equality atoms :   25 (  43 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ( ( k4_xboole_0 @ X21 @ X22 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X20: $i] :
      ( ( X18 = X20 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k4_xboole_0 @ X48 @ ( k1_tarski @ X49 ) )
        = X48 )
      | ( r2_hidden @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('10',plain,
    ( ( k1_xboole_0 = sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X36: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X39 @ X38 )
      | ( X39 = X36 )
      | ( X38
       != ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X36: $i,X39: $i] :
      ( ( X39 = X36 )
      | ~ ( r2_hidden @ X39 @ ( k1_tarski @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['7','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JbEXP8DOu4
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:37:37 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.39/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.60  % Solved by: fo/fo7.sh
% 0.39/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.60  % done 437 iterations in 0.134s
% 0.39/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.60  % SZS output start Refutation
% 0.39/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.60  thf(t66_zfmisc_1, conjecture,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.39/0.60          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.60    (~( ![A:$i,B:$i]:
% 0.39/0.60        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.39/0.60             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.39/0.60    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.39/0.60  thf('0', plain,
% 0.39/0.60      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(l32_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.60  thf('1', plain,
% 0.39/0.60      (![X21 : $i, X22 : $i]:
% 0.39/0.60         ((r1_tarski @ X21 @ X22)
% 0.39/0.60          | ((k4_xboole_0 @ X21 @ X22) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.60  thf('2', plain,
% 0.39/0.60      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.60        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.60  thf('3', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.39/0.60      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.60  thf(d10_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.60  thf('4', plain,
% 0.39/0.60      (![X18 : $i, X20 : $i]:
% 0.39/0.60         (((X18) = (X20))
% 0.39/0.60          | ~ (r1_tarski @ X20 @ X18)
% 0.39/0.60          | ~ (r1_tarski @ X18 @ X20))),
% 0.39/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.60  thf('5', plain,
% 0.39/0.60      ((~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.39/0.60        | ((k1_tarski @ sk_B) = (sk_A)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.60  thf('6', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('7', plain, (~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.39/0.60  thf('8', plain,
% 0.39/0.60      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(t65_zfmisc_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.39/0.60       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.39/0.60  thf('9', plain,
% 0.39/0.60      (![X48 : $i, X49 : $i]:
% 0.39/0.60         (((k4_xboole_0 @ X48 @ (k1_tarski @ X49)) = (X48))
% 0.39/0.60          | (r2_hidden @ X49 @ X48))),
% 0.39/0.60      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.39/0.60  thf('10', plain, ((((k1_xboole_0) = (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.39/0.60      inference('sup+', [status(thm)], ['8', '9'])).
% 0.39/0.60  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('12', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.39/0.60  thf(d3_tarski, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.60  thf('13', plain,
% 0.39/0.60      (![X3 : $i, X5 : $i]:
% 0.39/0.60         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.60  thf(d1_tarski, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.39/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.39/0.60  thf('14', plain,
% 0.39/0.60      (![X36 : $i, X38 : $i, X39 : $i]:
% 0.39/0.60         (~ (r2_hidden @ X39 @ X38)
% 0.39/0.60          | ((X39) = (X36))
% 0.39/0.60          | ((X38) != (k1_tarski @ X36)))),
% 0.39/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.60  thf('15', plain,
% 0.39/0.60      (![X36 : $i, X39 : $i]:
% 0.39/0.60         (((X39) = (X36)) | ~ (r2_hidden @ X39 @ (k1_tarski @ X36)))),
% 0.39/0.60      inference('simplify', [status(thm)], ['14'])).
% 0.39/0.60  thf('16', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.39/0.60          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['13', '15'])).
% 0.39/0.60  thf('17', plain,
% 0.39/0.60      (![X3 : $i, X5 : $i]:
% 0.39/0.60         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.39/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.60  thf('18', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.60          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.39/0.60          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.39/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.60  thf('19', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.39/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.39/0.60  thf('20', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.39/0.60      inference('sup-', [status(thm)], ['12', '19'])).
% 0.39/0.60  thf('21', plain, ($false), inference('demod', [status(thm)], ['7', '20'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
