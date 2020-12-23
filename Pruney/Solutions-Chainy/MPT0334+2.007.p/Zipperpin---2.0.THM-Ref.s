%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bPnbCjwafN

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:11 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  256 ( 299 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t141_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ ( k1_tarski @ X13 ) ) @ ( k1_tarski @ X13 ) )
        = X12 )
      | ( r2_hidden @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t141_zfmisc_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X3 )
      = ( k4_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ ( k1_tarski @ X13 ) )
        = X12 )
      | ( r2_hidden @ X13 @ X12 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t147_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( A != B )
       => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
          = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t147_zfmisc_1])).

thf('5',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('13',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bPnbCjwafN
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:26:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.63  % Solved by: fo/fo7.sh
% 0.38/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.63  % done 141 iterations in 0.164s
% 0.38/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.63  % SZS output start Refutation
% 0.38/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.63  thf(t141_zfmisc_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ~( r2_hidden @ A @ B ) ) =>
% 0.38/0.63       ( ( k4_xboole_0 @
% 0.38/0.63           ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.38/0.63         ( B ) ) ))).
% 0.38/0.63  thf('0', plain,
% 0.38/0.63      (![X12 : $i, X13 : $i]:
% 0.38/0.63         (((k4_xboole_0 @ (k2_xboole_0 @ X12 @ (k1_tarski @ X13)) @ 
% 0.38/0.63            (k1_tarski @ X13)) = (X12))
% 0.38/0.63          | (r2_hidden @ X13 @ X12))),
% 0.38/0.63      inference('cnf', [status(esa)], [t141_zfmisc_1])).
% 0.38/0.63  thf(t40_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.38/0.63  thf('1', plain,
% 0.38/0.63      (![X2 : $i, X3 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X3)
% 0.38/0.63           = (k4_xboole_0 @ X2 @ X3))),
% 0.38/0.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.38/0.63  thf('2', plain,
% 0.38/0.63      (![X12 : $i, X13 : $i]:
% 0.38/0.63         (((k4_xboole_0 @ X12 @ (k1_tarski @ X13)) = (X12))
% 0.38/0.63          | (r2_hidden @ X13 @ X12))),
% 0.38/0.63      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.63  thf(t42_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.38/0.63       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.38/0.63  thf('3', plain,
% 0.38/0.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X6) @ X5)
% 0.38/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X6 @ X5)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t42_xboole_1])).
% 0.38/0.63  thf('4', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.63         (((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k1_tarski @ X1))
% 0.38/0.63            = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X1)) @ X0))
% 0.38/0.63          | (r2_hidden @ X1 @ X0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.63  thf(t147_zfmisc_1, conjecture,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ( ( A ) != ( B ) ) =>
% 0.38/0.63       ( ( k4_xboole_0 @
% 0.38/0.63           ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 0.38/0.63         ( k2_xboole_0 @
% 0.38/0.63           ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ))).
% 0.38/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.63        ( ( ( A ) != ( B ) ) =>
% 0.38/0.63          ( ( k4_xboole_0 @
% 0.38/0.63              ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 0.38/0.63            ( k2_xboole_0 @
% 0.38/0.63              ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )),
% 0.38/0.63    inference('cnf.neg', [status(esa)], [t147_zfmisc_1])).
% 0.38/0.63  thf('5', plain,
% 0.38/0.63      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.38/0.63         (k1_tarski @ sk_B))
% 0.38/0.63         != (k2_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B)) @ 
% 0.38/0.63             (k1_tarski @ sk_A)))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf(commutativity_k2_xboole_0, axiom,
% 0.38/0.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.38/0.63  thf('6', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.63  thf('7', plain,
% 0.38/0.63      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.38/0.63         (k1_tarski @ sk_B))
% 0.38/0.63         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.38/0.63             (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B))))),
% 0.38/0.63      inference('demod', [status(thm)], ['5', '6'])).
% 0.38/0.63  thf('8', plain,
% 0.38/0.63      ((((k2_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B)) @ 
% 0.38/0.63          (k1_tarski @ sk_A))
% 0.38/0.63          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.38/0.63              (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B))))
% 0.38/0.63        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['4', '7'])).
% 0.38/0.63  thf('9', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.63  thf('10', plain,
% 0.38/0.63      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.38/0.63          (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B)))
% 0.38/0.63          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.38/0.63              (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B))))
% 0.38/0.63        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.38/0.63      inference('demod', [status(thm)], ['8', '9'])).
% 0.38/0.63  thf('11', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.38/0.63      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.63  thf(d1_tarski, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.63  thf('12', plain,
% 0.38/0.63      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X10 @ X9)
% 0.38/0.63          | ((X10) = (X7))
% 0.38/0.63          | ((X9) != (k1_tarski @ X7)))),
% 0.38/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.63  thf('13', plain,
% 0.38/0.63      (![X7 : $i, X10 : $i]:
% 0.38/0.63         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.38/0.63      inference('simplify', [status(thm)], ['12'])).
% 0.38/0.63  thf('14', plain, (((sk_B) = (sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['11', '13'])).
% 0.38/0.63  thf('15', plain, (((sk_A) != (sk_B))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('16', plain, ($false),
% 0.38/0.63      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.38/0.63  
% 0.38/0.63  % SZS output end Refutation
% 0.38/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
