%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q55bXZXuWR

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  141 ( 172 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t63_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X10 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X10: $i,X13: $i] :
      ( r2_hidden @ X10 @ ( k2_tarski @ X13 @ X10 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    $false ),
    inference(demod,[status(thm)],['0','10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q55bXZXuWR
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 21 iterations in 0.014s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(t63_zfmisc_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.21/0.46       ( r2_hidden @ A @ C ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.46        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.21/0.46          ( r2_hidden @ A @ C ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 0.21/0.46  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(d2_tarski, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.46       ( ![D:$i]:
% 0.21/0.46         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.46         (((X11) != (X10))
% 0.21/0.46          | (r2_hidden @ X11 @ X12)
% 0.21/0.46          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X10 : $i, X13 : $i]: (r2_hidden @ X10 @ (k2_tarski @ X13 @ X10))),
% 0.21/0.46      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.46         = (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(commutativity_k2_tarski, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.21/0.46      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.21/0.46      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (((k3_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C)
% 0.21/0.46         = (k2_tarski @ sk_B @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.46  thf(d4_xboole_0, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.46       ( ![D:$i]:
% 0.21/0.46         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.46           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.46          | (r2_hidden @ X4 @ X2)
% 0.21/0.46          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.46         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_A))
% 0.21/0.46          | (r2_hidden @ X0 @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.46  thf('10', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.46      inference('sup-', [status(thm)], ['2', '9'])).
% 0.21/0.46  thf('11', plain, ($false), inference('demod', [status(thm)], ['0', '10'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
