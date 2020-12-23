%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4D4b1kUMZ3

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:26 EST 2020

% Result     : Theorem 1.08s
% Output     : Refutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :   27 (  30 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :  235 ( 274 expanded)
%              Number of equality atoms :   36 (  43 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X55: $i,X56: $i] :
      ( ( X55 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X56 @ X55 ) @ X55 )
      | ( X55
        = ( k1_tarski @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( X22 = X19 )
      | ( X21
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22 = X19 )
      | ~ ( r2_hidden @ X22 @ ( k1_tarski @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C_1 @ X2 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X55: $i,X56: $i] :
      ( ( X55 = k1_xboole_0 )
      | ( ( sk_C_1 @ X56 @ X55 )
       != X56 )
      | ( X55
        = ( k1_tarski @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X2 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X2 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t69_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t69_zfmisc_1])).

thf('10',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4D4b1kUMZ3
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:20:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.08/1.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.08/1.31  % Solved by: fo/fo7.sh
% 1.08/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.08/1.31  % done 1331 iterations in 0.868s
% 1.08/1.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.08/1.31  % SZS output start Refutation
% 1.08/1.31  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.08/1.31  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.08/1.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.08/1.31  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.08/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.08/1.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.08/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.08/1.31  thf(t41_zfmisc_1, axiom,
% 1.08/1.31    (![A:$i,B:$i]:
% 1.08/1.31     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.08/1.31          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 1.08/1.31  thf('0', plain,
% 1.08/1.31      (![X55 : $i, X56 : $i]:
% 1.08/1.31         (((X55) = (k1_xboole_0))
% 1.08/1.31          | (r2_hidden @ (sk_C_1 @ X56 @ X55) @ X55)
% 1.08/1.31          | ((X55) = (k1_tarski @ X56)))),
% 1.08/1.31      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 1.08/1.31  thf(d5_xboole_0, axiom,
% 1.08/1.31    (![A:$i,B:$i,C:$i]:
% 1.08/1.31     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.08/1.31       ( ![D:$i]:
% 1.08/1.31         ( ( r2_hidden @ D @ C ) <=>
% 1.08/1.31           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.08/1.31  thf('1', plain,
% 1.08/1.31      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.08/1.31         (~ (r2_hidden @ X6 @ X5)
% 1.08/1.31          | (r2_hidden @ X6 @ X3)
% 1.08/1.31          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.08/1.31      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.08/1.31  thf('2', plain,
% 1.08/1.31      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.08/1.31         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.08/1.31      inference('simplify', [status(thm)], ['1'])).
% 1.08/1.31  thf('3', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.08/1.31         (((k4_xboole_0 @ X1 @ X0) = (k1_tarski @ X2))
% 1.08/1.31          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.08/1.31          | (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 1.08/1.31      inference('sup-', [status(thm)], ['0', '2'])).
% 1.08/1.31  thf(d1_tarski, axiom,
% 1.08/1.31    (![A:$i,B:$i]:
% 1.08/1.31     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.08/1.31       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.08/1.31  thf('4', plain,
% 1.08/1.31      (![X19 : $i, X21 : $i, X22 : $i]:
% 1.08/1.31         (~ (r2_hidden @ X22 @ X21)
% 1.08/1.31          | ((X22) = (X19))
% 1.08/1.31          | ((X21) != (k1_tarski @ X19)))),
% 1.08/1.31      inference('cnf', [status(esa)], [d1_tarski])).
% 1.08/1.31  thf('5', plain,
% 1.08/1.31      (![X19 : $i, X22 : $i]:
% 1.08/1.31         (((X22) = (X19)) | ~ (r2_hidden @ X22 @ (k1_tarski @ X19)))),
% 1.08/1.31      inference('simplify', [status(thm)], ['4'])).
% 1.08/1.31  thf('6', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.08/1.31         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 1.08/1.31          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X2))
% 1.08/1.31          | ((sk_C_1 @ X2 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)) = (X0)))),
% 1.08/1.31      inference('sup-', [status(thm)], ['3', '5'])).
% 1.08/1.31  thf('7', plain,
% 1.08/1.31      (![X55 : $i, X56 : $i]:
% 1.08/1.31         (((X55) = (k1_xboole_0))
% 1.08/1.31          | ((sk_C_1 @ X56 @ X55) != (X56))
% 1.08/1.31          | ((X55) = (k1_tarski @ X56)))),
% 1.08/1.31      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 1.08/1.31  thf('8', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.08/1.31         (((X0) != (X1))
% 1.08/1.31          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_tarski @ X1))
% 1.08/1.31          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0))
% 1.08/1.31          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_tarski @ X1))
% 1.08/1.31          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0)))),
% 1.08/1.31      inference('sup-', [status(thm)], ['6', '7'])).
% 1.08/1.31  thf('9', plain,
% 1.08/1.31      (![X1 : $i, X2 : $i]:
% 1.08/1.31         (((k4_xboole_0 @ (k1_tarski @ X1) @ X2) = (k1_xboole_0))
% 1.08/1.31          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X2) = (k1_tarski @ X1)))),
% 1.08/1.31      inference('simplify', [status(thm)], ['8'])).
% 1.08/1.31  thf(t69_zfmisc_1, conjecture,
% 1.08/1.31    (![A:$i,B:$i]:
% 1.08/1.31     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 1.08/1.31       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 1.08/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.08/1.31    (~( ![A:$i,B:$i]:
% 1.08/1.31        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 1.08/1.31          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 1.08/1.31    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 1.08/1.31  thf('10', plain,
% 1.08/1.31      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('11', plain,
% 1.08/1.31      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 1.08/1.31        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.08/1.31      inference('sup-', [status(thm)], ['9', '10'])).
% 1.08/1.31  thf('12', plain,
% 1.08/1.31      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 1.08/1.31      inference('simplify', [status(thm)], ['11'])).
% 1.08/1.31  thf('13', plain,
% 1.08/1.31      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('14', plain, ($false),
% 1.08/1.31      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 1.08/1.31  
% 1.08/1.31  % SZS output end Refutation
% 1.08/1.31  
% 1.08/1.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
