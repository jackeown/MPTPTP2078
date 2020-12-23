%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VHfptbKDIf

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  37 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  139 ( 231 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t24_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r1_tarski @ C @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) )
       => ! [C: $i] :
            ( ( r2_hidden @ C @ B )
           => ( r1_tarski @ C @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_setfam_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ ( sk_D @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_setfam_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r1_setfam_1 @ sk_B @ X0 )
      | ( r1_tarski @ sk_C_2 @ ( sk_D @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_C_2 @ ( sk_D @ sk_C_2 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_setfam_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D @ X5 @ X6 ) @ X6 )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_setfam_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D @ sk_C_2 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( sk_D @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference(demod,[status(thm)],['5','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VHfptbKDIf
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:51:03 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.21/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.43  % Solved by: fo/fo7.sh
% 0.21/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.43  % done 38 iterations in 0.012s
% 0.21/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.43  % SZS output start Refutation
% 0.21/0.43  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.43  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.43  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.21/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.43  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.43  thf(t24_setfam_1, conjecture,
% 0.21/0.43    (![A:$i,B:$i]:
% 0.21/0.43     ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.21/0.43       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.43    (~( ![A:$i,B:$i]:
% 0.21/0.43        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.21/0.43          ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ) )),
% 0.21/0.43    inference('cnf.neg', [status(esa)], [t24_setfam_1])).
% 0.21/0.43  thf('0', plain, (~ (r1_tarski @ sk_C_2 @ sk_A)),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf('1', plain, ((r1_setfam_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf('2', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf(d2_setfam_1, axiom,
% 0.21/0.43    (![A:$i,B:$i]:
% 0.21/0.43     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.21/0.43       ( ![C:$i]:
% 0.21/0.43         ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.43              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.43  thf('3', plain,
% 0.21/0.43      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.43         ((r1_tarski @ X5 @ (sk_D @ X5 @ X6))
% 0.21/0.43          | ~ (r2_hidden @ X5 @ X7)
% 0.21/0.43          | ~ (r1_setfam_1 @ X7 @ X6))),
% 0.21/0.43      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.43  thf('4', plain,
% 0.21/0.43      (![X0 : $i]:
% 0.21/0.43         (~ (r1_setfam_1 @ sk_B @ X0)
% 0.21/0.43          | (r1_tarski @ sk_C_2 @ (sk_D @ sk_C_2 @ X0)))),
% 0.21/0.43      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.43  thf('5', plain,
% 0.21/0.43      ((r1_tarski @ sk_C_2 @ (sk_D @ sk_C_2 @ (k1_tarski @ sk_A)))),
% 0.21/0.43      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.43  thf('6', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf('7', plain, ((r1_setfam_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf('8', plain,
% 0.21/0.43      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.43         ((r2_hidden @ (sk_D @ X5 @ X6) @ X6)
% 0.21/0.43          | ~ (r2_hidden @ X5 @ X7)
% 0.21/0.43          | ~ (r1_setfam_1 @ X7 @ X6))),
% 0.21/0.43      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.43  thf('9', plain,
% 0.21/0.43      (![X0 : $i]:
% 0.21/0.43         (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.43          | (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ sk_A)) @ (k1_tarski @ sk_A)))),
% 0.21/0.43      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.43  thf('10', plain,
% 0.21/0.43      ((r2_hidden @ (sk_D @ sk_C_2 @ (k1_tarski @ sk_A)) @ (k1_tarski @ sk_A))),
% 0.21/0.43      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.43  thf(d1_tarski, axiom,
% 0.21/0.43    (![A:$i,B:$i]:
% 0.21/0.43     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.43       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.43  thf('11', plain,
% 0.21/0.43      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.43         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.43      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.43  thf('12', plain,
% 0.21/0.43      (![X0 : $i, X3 : $i]:
% 0.21/0.43         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.43      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.43  thf('13', plain, (((sk_D @ sk_C_2 @ (k1_tarski @ sk_A)) = (sk_A))),
% 0.21/0.43      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.43  thf('14', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 0.21/0.43      inference('demod', [status(thm)], ['5', '13'])).
% 0.21/0.43  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 0.21/0.43  
% 0.21/0.43  % SZS output end Refutation
% 0.21/0.43  
% 0.21/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
