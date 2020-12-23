%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZE0yJEx1Sw

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:34 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  193 ( 247 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t27_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( ( k2_tarski @ A @ B )
        = ( k1_tarski @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( ( k2_tarski @ A @ B )
          = ( k1_tarski @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) )
    = ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k1_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k1_tarski @ X16 ) @ ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ~ ( r1_tarski @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('15',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k1_tarski @ X16 ) @ ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['4','15','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZE0yJEx1Sw
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 133 iterations in 0.069s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.34/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.52  thf(t27_zfmisc_1, conjecture,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.34/0.52       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.34/0.52        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.34/0.52          ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t27_zfmisc_1])).
% 0.34/0.52  thf('0', plain,
% 0.34/0.52      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(d10_xboole_0, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.52  thf('1', plain,
% 0.34/0.52      (![X2 : $i, X4 : $i]:
% 0.34/0.52         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.34/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      ((~ (r1_tarski @ (k1_tarski @ sk_C) @ (k2_tarski @ sk_A @ sk_B))
% 0.34/0.52        | ((k1_tarski @ sk_C) = (k2_tarski @ sk_A @ sk_B)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.34/0.52  thf('3', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('4', plain,
% 0.34/0.52      (~ (r1_tarski @ (k1_tarski @ sk_C) @ (k2_tarski @ sk_A @ sk_B))),
% 0.34/0.52      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.34/0.52  thf('5', plain,
% 0.34/0.52      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(t12_xboole_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.34/0.52  thf('6', plain,
% 0.34/0.52      (![X8 : $i, X9 : $i]:
% 0.34/0.52         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.34/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))
% 0.34/0.52         = (k1_tarski @ sk_C))),
% 0.34/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.52  thf(commutativity_k2_xboole_0, axiom,
% 0.34/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.34/0.52  thf('8', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.34/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.34/0.52  thf('9', plain,
% 0.34/0.52      (((k2_xboole_0 @ (k1_tarski @ sk_C) @ (k2_tarski @ sk_A @ sk_B))
% 0.34/0.52         = (k1_tarski @ sk_C))),
% 0.34/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.34/0.52  thf(t12_zfmisc_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      (![X16 : $i, X17 : $i]:
% 0.34/0.52         (r1_tarski @ (k1_tarski @ X16) @ (k2_tarski @ X16 @ X17))),
% 0.34/0.52      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.34/0.52  thf(t10_xboole_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.34/0.52  thf('11', plain,
% 0.34/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.34/0.52         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.34/0.52  thf('12', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         (r1_tarski @ (k1_tarski @ X1) @ 
% 0.34/0.52          (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.52  thf('13', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))),
% 0.34/0.52      inference('sup+', [status(thm)], ['9', '12'])).
% 0.34/0.52  thf(t6_zfmisc_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.34/0.52       ( ( A ) = ( B ) ) ))).
% 0.34/0.52  thf('14', plain,
% 0.34/0.52      (![X18 : $i, X19 : $i]:
% 0.34/0.52         (((X19) = (X18))
% 0.34/0.52          | ~ (r1_tarski @ (k1_tarski @ X19) @ (k1_tarski @ X18)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.34/0.52  thf('15', plain, (((sk_A) = (sk_C))),
% 0.34/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.34/0.52  thf('16', plain,
% 0.34/0.52      (![X16 : $i, X17 : $i]:
% 0.34/0.52         (r1_tarski @ (k1_tarski @ X16) @ (k2_tarski @ X16 @ X17))),
% 0.34/0.52      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.34/0.52  thf('17', plain, ($false),
% 0.34/0.52      inference('demod', [status(thm)], ['4', '15', '16'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.34/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
