%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cGQswnU4dW

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  48 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  148 ( 364 expanded)
%              Number of equality atoms :   16 (  34 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(t23_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ B )
         => ( A
            = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_tarski @ ( sk_C @ X0 ) @ ( sk_D @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( sk_A
      = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t8_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k4_tarski @ ( k1_mcart_1 @ X5 ) @ ( k2_mcart_1 @ X5 ) )
        = X5 )
      | ( X5
       != ( k4_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t8_mcart_1])).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_tarski @ ( k1_mcart_1 @ ( k4_tarski @ X6 @ X7 ) ) @ ( k2_mcart_1 @ ( k4_tarski @ X6 @ X7 ) ) )
      = ( k4_tarski @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ) @ ( k2_mcart_1 @ sk_A ) )
    = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('9',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('10',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    sk_A
 != ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cGQswnU4dW
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 7 iterations in 0.010s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i > $i).
% 0.20/0.46  thf(t23_mcart_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( r2_hidden @ A @ B ) =>
% 0.20/0.46         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( v1_relat_1 @ B ) =>
% 0.20/0.46          ( ( r2_hidden @ A @ B ) =>
% 0.20/0.46            ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t23_mcart_1])).
% 0.20/0.46  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d1_relat_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) <=>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.46              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (((X0) = (k4_tarski @ (sk_C @ X0) @ (sk_D @ X0)))
% 0.20/0.46          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.46          | ~ (v1_relat_1 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      ((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.46        | ((sk_A) = (k4_tarski @ (sk_C @ sk_A) @ (sk_D @ sk_A))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf('3', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('4', plain, (((sk_A) = (k4_tarski @ (sk_C @ sk_A) @ (sk_D @ sk_A)))),
% 0.20/0.46      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf(t8_mcart_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.46       ( ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         (((k4_tarski @ (k1_mcart_1 @ X5) @ (k2_mcart_1 @ X5)) = (X5))
% 0.20/0.46          | ((X5) != (k4_tarski @ X6 @ X7)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t8_mcart_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]:
% 0.20/0.46         ((k4_tarski @ (k1_mcart_1 @ (k4_tarski @ X6 @ X7)) @ 
% 0.20/0.46           (k2_mcart_1 @ (k4_tarski @ X6 @ X7))) = (k4_tarski @ X6 @ X7))),
% 0.20/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (((k4_tarski @ 
% 0.20/0.46         (k1_mcart_1 @ (k4_tarski @ (sk_C @ sk_A) @ (sk_D @ sk_A))) @ 
% 0.20/0.46         (k2_mcart_1 @ sk_A)) = (k4_tarski @ (sk_C @ sk_A) @ (sk_D @ sk_A)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.46  thf('8', plain, (((sk_A) = (k4_tarski @ (sk_C @ sk_A) @ (sk_D @ sk_A)))),
% 0.20/0.46      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf('9', plain, (((sk_A) = (k4_tarski @ (sk_C @ sk_A) @ (sk_D @ sk_A)))),
% 0.20/0.46      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)) = (sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (((sk_A) != (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('12', plain, ($false),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
