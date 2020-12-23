%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MXisfh2rRV

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:03 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   51 (  78 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  292 ( 529 expanded)
%              Number of equality atoms :   38 (  81 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k4_xboole_0 @ X53 @ ( k1_tarski @ X54 ) )
        = X53 )
      | ( r2_hidden @ X54 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('21',plain,
    ( ( k1_xboole_0 = sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('24',plain,(
    ! [X47: $i,X49: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X47 ) @ X49 )
      | ~ ( r2_hidden @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('25',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf('27',plain,
    ( ( k1_tarski @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['18','25','26'])).

thf('28',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MXisfh2rRV
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 162 iterations in 0.079s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(t66_zfmisc_1, conjecture,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.35/0.54          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i]:
% 0.35/0.54        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.35/0.54             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t100_xboole_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (![X7 : $i, X8 : $i]:
% 0.35/0.54         ((k4_xboole_0 @ X7 @ X8)
% 0.35/0.54           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.54  thf(t92_xboole_1, axiom,
% 0.35/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.54  thf('2', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.54  thf(t91_xboole_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.35/0.54       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.54         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.35/0.54           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.35/0.54           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['2', '3'])).
% 0.35/0.54  thf(commutativity_k5_xboole_0, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.35/0.54  thf(t5_boole, axiom,
% 0.35/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.54  thf('6', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.35/0.54      inference('cnf', [status(esa)], [t5_boole])).
% 0.35/0.54  thf('7', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.35/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.35/0.54      inference('demod', [status(thm)], ['4', '7'])).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((k3_xboole_0 @ X1 @ X0)
% 0.35/0.54           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['1', '8'])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.54         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.35/0.54      inference('sup+', [status(thm)], ['0', '9'])).
% 0.35/0.54  thf('11', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.35/0.54      inference('cnf', [status(esa)], [t5_boole])).
% 0.35/0.54  thf('12', plain, (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.35/0.54  thf(commutativity_k3_xboole_0, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.35/0.54  thf(t17_xboole_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 0.35/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.35/0.54      inference('sup+', [status(thm)], ['13', '14'])).
% 0.35/0.54  thf(d10_xboole_0, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (![X4 : $i, X6 : $i]:
% 0.35/0.54         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.35/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.35/0.54          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      ((~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.35/0.54        | ((k1_tarski @ sk_B) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['12', '17'])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t65_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.35/0.54       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (![X53 : $i, X54 : $i]:
% 0.35/0.54         (((k4_xboole_0 @ X53 @ (k1_tarski @ X54)) = (X53))
% 0.35/0.54          | (r2_hidden @ X54 @ X53))),
% 0.35/0.54      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.35/0.54  thf('21', plain, ((((k1_xboole_0) = (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.35/0.54      inference('sup+', [status(thm)], ['19', '20'])).
% 0.35/0.54  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('23', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.35/0.54  thf(l1_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      (![X47 : $i, X49 : $i]:
% 0.35/0.54         ((r1_tarski @ (k1_tarski @ X47) @ X49) | ~ (r2_hidden @ X47 @ X49))),
% 0.35/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.35/0.54  thf('25', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.35/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.54  thf('26', plain, (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.35/0.54  thf('27', plain, (((k1_tarski @ sk_B) = (sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['18', '25', '26'])).
% 0.35/0.54  thf('28', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('29', plain, ($false),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
