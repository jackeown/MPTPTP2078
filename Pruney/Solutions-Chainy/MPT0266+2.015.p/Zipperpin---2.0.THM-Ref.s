%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.feEuJuyPPB

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  160 ( 184 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
      ( ( X11 != X13 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X10: $i,X13: $i] :
      ( r2_hidden @ X13 @ ( k2_tarski @ X13 @ X10 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.feEuJuyPPB
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:34:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 40 iterations in 0.023s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.47  thf(t63_zfmisc_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.19/0.47       ( r2_hidden @ A @ C ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.47        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.19/0.47          ( r2_hidden @ A @ C ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 0.19/0.47  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d2_tarski, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.19/0.47       ( ![D:$i]:
% 0.19/0.47         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.47         (((X11) != (X13))
% 0.19/0.47          | (r2_hidden @ X11 @ X12)
% 0.19/0.47          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_tarski])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X10 : $i, X13 : $i]: (r2_hidden @ X13 @ (k2_tarski @ X13 @ X10))),
% 0.19/0.47      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.47         = (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.19/0.47         = (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf(t48_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X8 : $i, X9 : $i]:
% 0.19/0.47         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.19/0.47           = (k3_xboole_0 @ X8 @ X9))),
% 0.19/0.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.47  thf(d5_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.47       ( ![D:$i]:
% 0.19/0.47         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.47           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X6 @ X5)
% 0.19/0.47          | (r2_hidden @ X6 @ X3)
% 0.19/0.47          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.19/0.47         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['6', '8'])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.19/0.47          | (r2_hidden @ X0 @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['5', '9'])).
% 0.19/0.47  thf('11', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '10'])).
% 0.19/0.47  thf('12', plain, ($false), inference('demod', [status(thm)], ['0', '11'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
