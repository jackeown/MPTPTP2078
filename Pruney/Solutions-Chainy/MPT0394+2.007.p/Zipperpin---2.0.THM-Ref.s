%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0sTMeKLebR

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:45 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   53 (  95 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  334 ( 630 expanded)
%              Number of equality atoms :   44 (  80 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('2',plain,(
    ! [X32: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X30 @ X31 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X30 ) @ ( k1_setfam_1 @ X31 ) ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ( ( k3_xboole_0 @ X29 @ ( k1_tarski @ X28 ) )
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t51_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['9','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['4','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','23'])).

thf('25',plain,(
    ! [X32: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['9','21'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0sTMeKLebR
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 284 iterations in 0.202s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(t12_setfam_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i]:
% 0.45/0.65        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.45/0.65         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t41_enumset1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k2_tarski @ A @ B ) =
% 0.45/0.65       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X21 : $i, X22 : $i]:
% 0.45/0.65         ((k2_tarski @ X21 @ X22)
% 0.45/0.65           = (k2_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X22)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.45/0.65  thf(t11_setfam_1, axiom,
% 0.45/0.65    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.45/0.65  thf('2', plain, (![X32 : $i]: ((k1_setfam_1 @ (k1_tarski @ X32)) = (X32))),
% 0.45/0.65      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.45/0.65  thf(t10_setfam_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.45/0.65          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.45/0.65            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X30 : $i, X31 : $i]:
% 0.45/0.65         (((X30) = (k1_xboole_0))
% 0.45/0.65          | ((k1_setfam_1 @ (k2_xboole_0 @ X30 @ X31))
% 0.45/0.65              = (k3_xboole_0 @ (k1_setfam_1 @ X30) @ (k1_setfam_1 @ X31)))
% 0.45/0.65          | ((X31) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.45/0.65            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.45/0.65          | ((X1) = (k1_xboole_0))
% 0.45/0.65          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['2', '3'])).
% 0.45/0.65  thf(t48_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X12 : $i, X13 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.45/0.65           = (k3_xboole_0 @ X12 @ X13))),
% 0.45/0.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.65  thf(t4_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X14 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_boole])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['5', '6'])).
% 0.45/0.65  thf(t51_zfmisc_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.45/0.65       ( r2_hidden @ B @ A ) ))).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X28 : $i, X29 : $i]:
% 0.45/0.65         ((r2_hidden @ X28 @ X29)
% 0.45/0.65          | ((k3_xboole_0 @ X29 @ (k1_tarski @ X28)) != (k1_tarski @ X28)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t51_zfmisc_1])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['5', '6'])).
% 0.45/0.65  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.65  thf(t4_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.45/0.65          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.65          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '13'])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['5', '6'])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.65  thf(d7_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.45/0.65       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X2 : $i, X4 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['15', '18'])).
% 0.45/0.65  thf('20', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.45/0.65      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.65  thf('21', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['14', '20'])).
% 0.45/0.65  thf('22', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.45/0.65      inference('clc', [status(thm)], ['9', '21'])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X1) = (k1_xboole_0))
% 0.45/0.65          | ((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.45/0.65              = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1))))),
% 0.45/0.65      inference('clc', [status(thm)], ['4', '22'])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.45/0.65            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.45/0.65          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['1', '23'])).
% 0.45/0.65  thf('25', plain, (![X32 : $i]: ((k1_setfam_1 @ (k1_tarski @ X32)) = (X32))),
% 0.45/0.65      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.45/0.65          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.65  thf('27', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.45/0.65      inference('clc', [status(thm)], ['9', '21'])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('clc', [status(thm)], ['26', '27'])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['0', '28'])).
% 0.45/0.65  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
