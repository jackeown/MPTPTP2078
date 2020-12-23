%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o5FWy0nYH3

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:16 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   53 (  65 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  341 ( 512 expanded)
%              Number of equality atoms :   37 (  57 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ ( k4_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k3_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B_1 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t53_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r2_hidden @ X54 @ X53 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X52 @ X54 ) @ X53 )
        = ( k2_tarski @ X52 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t53_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_D_1 @ X0 ) @ sk_A )
        = ( k2_tarski @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_D_1 @ X0 ) )
        = ( k2_tarski @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_D_1 @ sk_D_1 ) )
    = ( k2_tarski @ sk_D_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['16','26'])).

thf('28',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o5FWy0nYH3
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.43/1.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.43/1.62  % Solved by: fo/fo7.sh
% 1.43/1.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.43/1.62  % done 2268 iterations in 1.142s
% 1.43/1.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.43/1.62  % SZS output start Refutation
% 1.43/1.62  thf(sk_A_type, type, sk_A: $i).
% 1.43/1.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.43/1.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.43/1.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.43/1.62  thf(sk_C_type, type, sk_C: $i).
% 1.43/1.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.43/1.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.43/1.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.43/1.62  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.43/1.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.43/1.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.43/1.62  thf(t148_zfmisc_1, conjecture,
% 1.43/1.62    (![A:$i,B:$i,C:$i,D:$i]:
% 1.43/1.62     ( ( ( r1_tarski @ A @ B ) & 
% 1.43/1.62         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.43/1.62         ( r2_hidden @ D @ A ) ) =>
% 1.43/1.62       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 1.43/1.62  thf(zf_stmt_0, negated_conjecture,
% 1.43/1.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.43/1.62        ( ( ( r1_tarski @ A @ B ) & 
% 1.43/1.62            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.43/1.62            ( r2_hidden @ D @ A ) ) =>
% 1.43/1.62          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 1.43/1.62    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 1.43/1.62  thf('0', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C) = (k1_tarski @ sk_D_1))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf(commutativity_k3_xboole_0, axiom,
% 1.43/1.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.43/1.62  thf('1', plain,
% 1.43/1.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.43/1.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.43/1.62  thf(t48_xboole_1, axiom,
% 1.43/1.62    (![A:$i,B:$i]:
% 1.43/1.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.43/1.62  thf('2', plain,
% 1.43/1.62      (![X22 : $i, X23 : $i]:
% 1.43/1.62         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.43/1.62           = (k3_xboole_0 @ X22 @ X23))),
% 1.43/1.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.43/1.62  thf('3', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf(t109_xboole_1, axiom,
% 1.43/1.62    (![A:$i,B:$i,C:$i]:
% 1.43/1.62     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 1.43/1.62  thf('4', plain,
% 1.43/1.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.43/1.62         (~ (r1_tarski @ X9 @ X10)
% 1.43/1.62          | (r1_tarski @ (k4_xboole_0 @ X9 @ X11) @ X10))),
% 1.43/1.62      inference('cnf', [status(esa)], [t109_xboole_1])).
% 1.43/1.62  thf('5', plain,
% 1.43/1.62      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1)),
% 1.43/1.62      inference('sup-', [status(thm)], ['3', '4'])).
% 1.43/1.62  thf(t12_xboole_1, axiom,
% 1.43/1.62    (![A:$i,B:$i]:
% 1.43/1.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.43/1.62  thf('6', plain,
% 1.43/1.62      (![X12 : $i, X13 : $i]:
% 1.43/1.62         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 1.43/1.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.43/1.62  thf('7', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         ((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1) = (sk_B_1))),
% 1.43/1.62      inference('sup-', [status(thm)], ['5', '6'])).
% 1.43/1.62  thf('8', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         ((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B_1) = (sk_B_1))),
% 1.43/1.62      inference('sup+', [status(thm)], ['2', '7'])).
% 1.43/1.62  thf(t21_xboole_1, axiom,
% 1.43/1.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.43/1.62  thf('9', plain,
% 1.43/1.62      (![X17 : $i, X18 : $i]:
% 1.43/1.62         ((k3_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (X17))),
% 1.43/1.62      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.43/1.62  thf('10', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 1.43/1.62           = (k3_xboole_0 @ sk_A @ X0))),
% 1.43/1.62      inference('sup+', [status(thm)], ['8', '9'])).
% 1.43/1.62  thf(t16_xboole_1, axiom,
% 1.43/1.62    (![A:$i,B:$i,C:$i]:
% 1.43/1.62     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.43/1.62       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.43/1.62  thf('11', plain,
% 1.43/1.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.43/1.62         ((k3_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16)
% 1.43/1.62           = (k3_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16)))),
% 1.43/1.62      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.43/1.62  thf('12', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B_1))
% 1.43/1.62           = (k3_xboole_0 @ sk_A @ X0))),
% 1.43/1.62      inference('demod', [status(thm)], ['10', '11'])).
% 1.43/1.62  thf('13', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ X0))
% 1.43/1.62           = (k3_xboole_0 @ sk_A @ X0))),
% 1.43/1.62      inference('sup+', [status(thm)], ['1', '12'])).
% 1.43/1.62  thf('14', plain,
% 1.43/1.62      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))
% 1.43/1.62         = (k3_xboole_0 @ sk_A @ sk_C))),
% 1.43/1.62      inference('sup+', [status(thm)], ['0', '13'])).
% 1.43/1.62  thf('15', plain,
% 1.43/1.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.43/1.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.43/1.62  thf('16', plain,
% 1.43/1.62      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))
% 1.43/1.62         = (k3_xboole_0 @ sk_C @ sk_A))),
% 1.43/1.62      inference('demod', [status(thm)], ['14', '15'])).
% 1.43/1.62  thf('17', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('18', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf(t53_zfmisc_1, axiom,
% 1.43/1.62    (![A:$i,B:$i,C:$i]:
% 1.43/1.62     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 1.43/1.62       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 1.43/1.62  thf('19', plain,
% 1.43/1.62      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.43/1.62         (~ (r2_hidden @ X52 @ X53)
% 1.43/1.62          | ~ (r2_hidden @ X54 @ X53)
% 1.43/1.62          | ((k3_xboole_0 @ (k2_tarski @ X52 @ X54) @ X53)
% 1.43/1.62              = (k2_tarski @ X52 @ X54)))),
% 1.43/1.62      inference('cnf', [status(esa)], [t53_zfmisc_1])).
% 1.43/1.62  thf('20', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         (((k3_xboole_0 @ (k2_tarski @ sk_D_1 @ X0) @ sk_A)
% 1.43/1.62            = (k2_tarski @ sk_D_1 @ X0))
% 1.43/1.62          | ~ (r2_hidden @ X0 @ sk_A))),
% 1.43/1.62      inference('sup-', [status(thm)], ['18', '19'])).
% 1.43/1.62  thf('21', plain,
% 1.43/1.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.43/1.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.43/1.62  thf('22', plain,
% 1.43/1.62      (![X0 : $i]:
% 1.43/1.62         (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_D_1 @ X0))
% 1.43/1.62            = (k2_tarski @ sk_D_1 @ X0))
% 1.43/1.62          | ~ (r2_hidden @ X0 @ sk_A))),
% 1.43/1.62      inference('demod', [status(thm)], ['20', '21'])).
% 1.43/1.62  thf('23', plain,
% 1.43/1.62      (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_D_1 @ sk_D_1))
% 1.43/1.62         = (k2_tarski @ sk_D_1 @ sk_D_1))),
% 1.43/1.62      inference('sup-', [status(thm)], ['17', '22'])).
% 1.43/1.62  thf(t69_enumset1, axiom,
% 1.43/1.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.43/1.62  thf('24', plain,
% 1.43/1.62      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 1.43/1.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.43/1.62  thf('25', plain,
% 1.43/1.62      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 1.43/1.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.43/1.62  thf('26', plain,
% 1.43/1.62      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)) = (k1_tarski @ sk_D_1))),
% 1.43/1.62      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.43/1.62  thf('27', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D_1))),
% 1.43/1.62      inference('sup+', [status(thm)], ['16', '26'])).
% 1.43/1.62  thf('28', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D_1))),
% 1.43/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.62  thf('29', plain,
% 1.43/1.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.43/1.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.43/1.62  thf('30', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D_1))),
% 1.43/1.62      inference('demod', [status(thm)], ['28', '29'])).
% 1.43/1.62  thf('31', plain, ($false),
% 1.43/1.62      inference('simplify_reflect-', [status(thm)], ['27', '30'])).
% 1.43/1.62  
% 1.43/1.62  % SZS output end Refutation
% 1.43/1.62  
% 1.43/1.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
