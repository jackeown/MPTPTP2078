%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mkNNZbiCaC

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :  105 ( 119 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t54_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
          & ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t54_zfmisc_1])).

thf('0',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('3',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X4 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    $false ),
    inference(demod,[status(thm)],['7','8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mkNNZbiCaC
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.43  % Solved by: fo/fo7.sh
% 0.21/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.43  % done 13 iterations in 0.007s
% 0.21/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.43  % SZS output start Refutation
% 0.21/0.43  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.43  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.43  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.43  thf(t54_zfmisc_1, conjecture,
% 0.21/0.43    (![A:$i,B:$i]:
% 0.21/0.43     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.43    (~( ![A:$i,B:$i]:
% 0.21/0.43        ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ) )),
% 0.21/0.43    inference('cnf.neg', [status(esa)], [t54_zfmisc_1])).
% 0.21/0.43  thf('0', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf(t69_enumset1, axiom,
% 0.21/0.43    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.43  thf('1', plain, (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.21/0.43      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.43  thf(d2_tarski, axiom,
% 0.21/0.43    (![A:$i,B:$i,C:$i]:
% 0.21/0.43     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.43       ( ![D:$i]:
% 0.21/0.43         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.43  thf('2', plain,
% 0.21/0.43      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.43         (((X5) != (X4))
% 0.21/0.43          | (r2_hidden @ X5 @ X6)
% 0.21/0.43          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.21/0.43      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.43  thf('3', plain,
% 0.21/0.43      (![X4 : $i, X7 : $i]: (r2_hidden @ X4 @ (k2_tarski @ X7 @ X4))),
% 0.21/0.43      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.43  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.43      inference('sup+', [status(thm)], ['1', '3'])).
% 0.21/0.43  thf(t3_xboole_0, axiom,
% 0.21/0.43    (![A:$i,B:$i]:
% 0.21/0.43     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.43            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.43       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.43            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.43  thf('5', plain,
% 0.21/0.43      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.43         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.43          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.43          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.43      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.43  thf('6', plain,
% 0.21/0.43      (![X0 : $i, X1 : $i]:
% 0.21/0.43         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.43      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.43  thf('7', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.21/0.43      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.43  thf('8', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf('9', plain, ($false), inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.43  
% 0.21/0.43  % SZS output end Refutation
% 0.21/0.43  
% 0.21/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
