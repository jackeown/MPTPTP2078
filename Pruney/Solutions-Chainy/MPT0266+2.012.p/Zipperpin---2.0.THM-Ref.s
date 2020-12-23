%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EzAoZ13QzK

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  208 ( 232 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('1',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = sk_C ),
    inference('sup+',[status(thm)],['3','8'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X17 )
      | ( r2_hidden @ X15 @ X16 )
      | ( X16
       != ( k2_tarski @ X17 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('11',plain,(
    ! [X14: $i,X17: $i] :
      ( r2_hidden @ X17 @ ( k2_tarski @ X17 @ X14 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EzAoZ13QzK
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:32:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 58 iterations in 0.052s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(t63_zfmisc_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.20/0.51       ( r2_hidden @ A @ C ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.20/0.51          ( r2_hidden @ A @ C ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 0.20/0.51  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.20/0.51         = (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.51         = (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.51  thf('4', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ X8) = (X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.51  thf(t24_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.20/0.51       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.51         ((k2_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13))
% 0.20/0.51           = (k3_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ 
% 0.20/0.51              (k2_xboole_0 @ X11 @ X13)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t24_xboole_1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.20/0.51           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf(t21_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (sk_C))),
% 0.20/0.51      inference('sup+', [status(thm)], ['3', '8'])).
% 0.20/0.51  thf(d2_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.51         (((X15) != (X17))
% 0.20/0.51          | (r2_hidden @ X15 @ X16)
% 0.20/0.51          | ((X16) != (k2_tarski @ X17 @ X14)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X14 : $i, X17 : $i]: (r2_hidden @ X17 @ (k2_tarski @ X17 @ X14))),
% 0.20/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.51  thf(d3_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.51          | (r2_hidden @ X2 @ X4)
% 0.20/0.51          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.51         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (r2_hidden @ X1 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.51  thf('15', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.20/0.51      inference('sup+', [status(thm)], ['9', '14'])).
% 0.20/0.51  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
