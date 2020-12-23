%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OZOhfaUiKm

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  50 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  268 ( 334 expanded)
%              Number of equality atoms :   28 (  34 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t144_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X15 @ X17 ) @ X18 )
        = ( k2_tarski @ X15 @ X17 ) )
      | ( r2_hidden @ X17 @ X18 )
      | ( r2_hidden @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf('19',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OZOhfaUiKm
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.70  % Solved by: fo/fo7.sh
% 0.21/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.70  % done 627 iterations in 0.251s
% 0.21/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.70  % SZS output start Refutation
% 0.21/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.70  thf(t144_zfmisc_1, conjecture,
% 0.21/0.70    (![A:$i,B:$i,C:$i]:
% 0.21/0.70     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.21/0.70          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.21/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.70        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.21/0.70             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.21/0.70    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 0.21/0.70  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.21/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.70  thf(t72_zfmisc_1, axiom,
% 0.21/0.70    (![A:$i,B:$i,C:$i]:
% 0.21/0.70     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.70       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.21/0.70  thf('1', plain,
% 0.21/0.70      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.21/0.70         (((k4_xboole_0 @ (k2_tarski @ X15 @ X17) @ X18)
% 0.21/0.70            = (k2_tarski @ X15 @ X17))
% 0.21/0.70          | (r2_hidden @ X17 @ X18)
% 0.21/0.70          | (r2_hidden @ X15 @ X18))),
% 0.21/0.70      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.21/0.70  thf(t79_xboole_1, axiom,
% 0.21/0.70    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.70  thf('2', plain,
% 0.21/0.70      (![X8 : $i, X9 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X9)),
% 0.21/0.70      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.70  thf(t83_xboole_1, axiom,
% 0.21/0.70    (![A:$i,B:$i]:
% 0.21/0.70     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.70  thf('3', plain,
% 0.21/0.70      (![X10 : $i, X11 : $i]:
% 0.21/0.70         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.21/0.70      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.70  thf('4', plain,
% 0.21/0.70      (![X0 : $i, X1 : $i]:
% 0.21/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.21/0.70           = (k4_xboole_0 @ X1 @ X0))),
% 0.21/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.70  thf(t48_xboole_1, axiom,
% 0.21/0.70    (![A:$i,B:$i]:
% 0.21/0.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.70  thf('5', plain,
% 0.21/0.70      (![X6 : $i, X7 : $i]:
% 0.21/0.70         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.21/0.70           = (k3_xboole_0 @ X6 @ X7))),
% 0.21/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.70  thf('6', plain,
% 0.21/0.70      (![X0 : $i, X1 : $i]:
% 0.21/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.21/0.70           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.21/0.70      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.70  thf(t3_boole, axiom,
% 0.21/0.70    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.70  thf('7', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.21/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.70  thf('8', plain,
% 0.21/0.70      (![X6 : $i, X7 : $i]:
% 0.21/0.70         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.21/0.70           = (k3_xboole_0 @ X6 @ X7))),
% 0.21/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.70  thf('9', plain,
% 0.21/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.70      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.70  thf(t2_boole, axiom,
% 0.21/0.70    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.70  thf('10', plain,
% 0.21/0.70      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.70      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.70  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.70      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.70  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.70  thf('12', plain,
% 0.21/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.70  thf('13', plain,
% 0.21/0.70      (![X0 : $i, X1 : $i]:
% 0.21/0.70         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.70      inference('demod', [status(thm)], ['6', '11', '12'])).
% 0.21/0.70  thf(t47_xboole_1, axiom,
% 0.21/0.70    (![A:$i,B:$i]:
% 0.21/0.70     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.70  thf('14', plain,
% 0.21/0.70      (![X4 : $i, X5 : $i]:
% 0.21/0.70         ((k4_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5))
% 0.21/0.70           = (k4_xboole_0 @ X4 @ X5))),
% 0.21/0.70      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.70  thf('15', plain,
% 0.21/0.70      (![X0 : $i, X1 : $i]:
% 0.21/0.70         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.21/0.70           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.70      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.70  thf('16', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.21/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.70  thf('17', plain,
% 0.21/0.70      (![X0 : $i, X1 : $i]:
% 0.21/0.70         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.70      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.70  thf('18', plain,
% 0.21/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.70         (((X2) = (k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))
% 0.21/0.70          | (r2_hidden @ X1 @ X2)
% 0.21/0.70          | (r2_hidden @ X0 @ X2))),
% 0.21/0.70      inference('sup+', [status(thm)], ['1', '17'])).
% 0.21/0.70  thf('19', plain,
% 0.21/0.70      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.70  thf('20', plain,
% 0.21/0.70      ((((sk_C) != (sk_C))
% 0.21/0.70        | (r2_hidden @ sk_B @ sk_C)
% 0.21/0.70        | (r2_hidden @ sk_A @ sk_C))),
% 0.21/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.70  thf('21', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 0.21/0.70      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.70  thf('22', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.21/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.70  thf('23', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.21/0.70      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.70  thf('24', plain, ($false), inference('demod', [status(thm)], ['0', '23'])).
% 0.21/0.70  
% 0.21/0.70  % SZS output end Refutation
% 0.21/0.70  
% 0.21/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
