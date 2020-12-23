%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VUf6b3IG7D

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:33 EST 2020

% Result     : Theorem 20.85s
% Output     : Refutation 20.85s
% Verified   : 
% Statistics : Number of formulae       :   56 (  71 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  368 ( 486 expanded)
%              Number of equality atoms :   36 (  53 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
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

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X35 != X34 )
      | ( r2_hidden @ X35 @ X36 )
      | ( X36
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X34: $i] :
      ( r2_hidden @ X34 @ ( k1_tarski @ X34 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k5_xboole_0 @ X6 @ X8 ) )
      | ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X50 ) @ X49 )
        = X49 )
      | ~ ( r2_hidden @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('13',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X37 @ X36 )
      | ( X37 = X34 )
      | ( X36
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('21',plain,(
    ! [X34: $i,X37: $i] :
      ( ( X37 = X34 )
      | ~ ( r2_hidden @ X37 @ ( k1_tarski @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X34: $i] :
      ( r2_hidden @ X34 @ ( k1_tarski @ X34 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('26',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('33',plain,(
    ! [X2: $i] :
      ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('sup-',[status(thm)],['26','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VUf6b3IG7D
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:52:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 20.85/21.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 20.85/21.05  % Solved by: fo/fo7.sh
% 20.85/21.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.85/21.05  % done 9429 iterations in 20.594s
% 20.85/21.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 20.85/21.05  % SZS output start Refutation
% 20.85/21.05  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 20.85/21.05  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 20.85/21.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 20.85/21.05  thf(sk_A_type, type, sk_A: $i).
% 20.85/21.05  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 20.85/21.05  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 20.85/21.05  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 20.85/21.05  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 20.85/21.05  thf(sk_B_type, type, sk_B: $i).
% 20.85/21.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 20.85/21.05  thf(t18_zfmisc_1, conjecture,
% 20.85/21.05    (![A:$i,B:$i]:
% 20.85/21.05     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 20.85/21.05         ( k1_tarski @ A ) ) =>
% 20.85/21.05       ( ( A ) = ( B ) ) ))).
% 20.85/21.05  thf(zf_stmt_0, negated_conjecture,
% 20.85/21.05    (~( ![A:$i,B:$i]:
% 20.85/21.05        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 20.85/21.05            ( k1_tarski @ A ) ) =>
% 20.85/21.05          ( ( A ) = ( B ) ) ) )),
% 20.85/21.05    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 20.85/21.05  thf('0', plain,
% 20.85/21.05      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 20.85/21.05         = (k1_tarski @ sk_A))),
% 20.85/21.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.85/21.05  thf(commutativity_k3_xboole_0, axiom,
% 20.85/21.05    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 20.85/21.05  thf('1', plain,
% 20.85/21.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.85/21.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.85/21.05  thf('2', plain,
% 20.85/21.05      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 20.85/21.05         = (k1_tarski @ sk_A))),
% 20.85/21.05      inference('demod', [status(thm)], ['0', '1'])).
% 20.85/21.05  thf(t100_xboole_1, axiom,
% 20.85/21.05    (![A:$i,B:$i]:
% 20.85/21.05     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 20.85/21.05  thf('3', plain,
% 20.85/21.05      (![X13 : $i, X14 : $i]:
% 20.85/21.05         ((k4_xboole_0 @ X13 @ X14)
% 20.85/21.05           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 20.85/21.05      inference('cnf', [status(esa)], [t100_xboole_1])).
% 20.85/21.05  thf('4', plain,
% 20.85/21.05      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 20.85/21.05         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 20.85/21.05      inference('sup+', [status(thm)], ['2', '3'])).
% 20.85/21.05  thf(d1_tarski, axiom,
% 20.85/21.05    (![A:$i,B:$i]:
% 20.85/21.05     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 20.85/21.05       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 20.85/21.05  thf('5', plain,
% 20.85/21.05      (![X34 : $i, X35 : $i, X36 : $i]:
% 20.85/21.05         (((X35) != (X34))
% 20.85/21.05          | (r2_hidden @ X35 @ X36)
% 20.85/21.05          | ((X36) != (k1_tarski @ X34)))),
% 20.85/21.05      inference('cnf', [status(esa)], [d1_tarski])).
% 20.85/21.05  thf('6', plain, (![X34 : $i]: (r2_hidden @ X34 @ (k1_tarski @ X34))),
% 20.85/21.05      inference('simplify', [status(thm)], ['5'])).
% 20.85/21.05  thf(t1_xboole_0, axiom,
% 20.85/21.05    (![A:$i,B:$i,C:$i]:
% 20.85/21.05     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 20.85/21.05       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 20.85/21.05  thf('7', plain,
% 20.85/21.05      (![X5 : $i, X6 : $i, X8 : $i]:
% 20.85/21.05         ((r2_hidden @ X5 @ (k5_xboole_0 @ X6 @ X8))
% 20.85/21.05          | (r2_hidden @ X5 @ X6)
% 20.85/21.05          | ~ (r2_hidden @ X5 @ X8))),
% 20.85/21.05      inference('cnf', [status(esa)], [t1_xboole_0])).
% 20.85/21.05  thf('8', plain,
% 20.85/21.05      (![X0 : $i, X1 : $i]:
% 20.85/21.05         ((r2_hidden @ X0 @ X1)
% 20.85/21.05          | (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 20.85/21.05      inference('sup-', [status(thm)], ['6', '7'])).
% 20.85/21.05  thf('9', plain,
% 20.85/21.05      (((r2_hidden @ sk_A @ 
% 20.85/21.05         (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 20.85/21.05        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 20.85/21.05      inference('sup+', [status(thm)], ['4', '8'])).
% 20.85/21.05  thf(l22_zfmisc_1, axiom,
% 20.85/21.05    (![A:$i,B:$i]:
% 20.85/21.05     ( ( r2_hidden @ A @ B ) =>
% 20.85/21.05       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 20.85/21.05  thf('10', plain,
% 20.85/21.05      (![X49 : $i, X50 : $i]:
% 20.85/21.05         (((k2_xboole_0 @ (k1_tarski @ X50) @ X49) = (X49))
% 20.85/21.05          | ~ (r2_hidden @ X50 @ X49))),
% 20.85/21.05      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 20.85/21.05  thf('11', plain,
% 20.85/21.05      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B))
% 20.85/21.05        | ((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 20.85/21.05            (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 20.85/21.05            = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))),
% 20.85/21.05      inference('sup-', [status(thm)], ['9', '10'])).
% 20.85/21.05  thf(t21_xboole_1, axiom,
% 20.85/21.05    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 20.85/21.05  thf('12', plain,
% 20.85/21.05      (![X18 : $i, X19 : $i]:
% 20.85/21.05         ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (X18))),
% 20.85/21.05      inference('cnf', [status(esa)], [t21_xboole_1])).
% 20.85/21.05  thf('13', plain,
% 20.85/21.05      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 20.85/21.05          (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 20.85/21.05          = (k1_tarski @ sk_A))
% 20.85/21.05        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 20.85/21.05      inference('sup+', [status(thm)], ['11', '12'])).
% 20.85/21.05  thf(t79_xboole_1, axiom,
% 20.85/21.05    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 20.85/21.05  thf('14', plain,
% 20.85/21.05      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 20.85/21.05      inference('cnf', [status(esa)], [t79_xboole_1])).
% 20.85/21.05  thf(d7_xboole_0, axiom,
% 20.85/21.05    (![A:$i,B:$i]:
% 20.85/21.05     ( ( r1_xboole_0 @ A @ B ) <=>
% 20.85/21.05       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 20.85/21.05  thf('15', plain,
% 20.85/21.05      (![X2 : $i, X3 : $i]:
% 20.85/21.05         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 20.85/21.05      inference('cnf', [status(esa)], [d7_xboole_0])).
% 20.85/21.05  thf('16', plain,
% 20.85/21.05      (![X0 : $i, X1 : $i]:
% 20.85/21.05         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 20.85/21.05      inference('sup-', [status(thm)], ['14', '15'])).
% 20.85/21.05  thf('17', plain,
% 20.85/21.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.85/21.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.85/21.05  thf('18', plain,
% 20.85/21.05      (![X0 : $i, X1 : $i]:
% 20.85/21.05         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 20.85/21.05      inference('demod', [status(thm)], ['16', '17'])).
% 20.85/21.05  thf('19', plain,
% 20.85/21.05      ((((k1_xboole_0) = (k1_tarski @ sk_A))
% 20.85/21.05        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 20.85/21.05      inference('demod', [status(thm)], ['13', '18'])).
% 20.85/21.05  thf('20', plain,
% 20.85/21.05      (![X34 : $i, X36 : $i, X37 : $i]:
% 20.85/21.05         (~ (r2_hidden @ X37 @ X36)
% 20.85/21.05          | ((X37) = (X34))
% 20.85/21.05          | ((X36) != (k1_tarski @ X34)))),
% 20.85/21.05      inference('cnf', [status(esa)], [d1_tarski])).
% 20.85/21.05  thf('21', plain,
% 20.85/21.05      (![X34 : $i, X37 : $i]:
% 20.85/21.05         (((X37) = (X34)) | ~ (r2_hidden @ X37 @ (k1_tarski @ X34)))),
% 20.85/21.05      inference('simplify', [status(thm)], ['20'])).
% 20.85/21.05  thf('22', plain,
% 20.85/21.05      ((((k1_xboole_0) = (k1_tarski @ sk_A)) | ((sk_A) = (sk_B)))),
% 20.85/21.05      inference('sup-', [status(thm)], ['19', '21'])).
% 20.85/21.05  thf('23', plain, (((sk_A) != (sk_B))),
% 20.85/21.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.85/21.05  thf('24', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 20.85/21.05      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 20.85/21.05  thf('25', plain, (![X34 : $i]: (r2_hidden @ X34 @ (k1_tarski @ X34))),
% 20.85/21.05      inference('simplify', [status(thm)], ['5'])).
% 20.85/21.05  thf('26', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 20.85/21.05      inference('sup+', [status(thm)], ['24', '25'])).
% 20.85/21.05  thf('27', plain,
% 20.85/21.05      (![X0 : $i, X1 : $i]:
% 20.85/21.05         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 20.85/21.05      inference('demod', [status(thm)], ['16', '17'])).
% 20.85/21.05  thf('28', plain,
% 20.85/21.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.85/21.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.85/21.05  thf(t4_xboole_0, axiom,
% 20.85/21.05    (![A:$i,B:$i]:
% 20.85/21.05     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 20.85/21.05            ( r1_xboole_0 @ A @ B ) ) ) & 
% 20.85/21.05       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 20.85/21.05            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 20.85/21.05  thf('29', plain,
% 20.85/21.05      (![X9 : $i, X11 : $i, X12 : $i]:
% 20.85/21.05         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 20.85/21.05          | ~ (r1_xboole_0 @ X9 @ X12))),
% 20.85/21.05      inference('cnf', [status(esa)], [t4_xboole_0])).
% 20.85/21.05  thf('30', plain,
% 20.85/21.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.85/21.05         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 20.85/21.05          | ~ (r1_xboole_0 @ X0 @ X1))),
% 20.85/21.05      inference('sup-', [status(thm)], ['28', '29'])).
% 20.85/21.05  thf('31', plain,
% 20.85/21.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.85/21.05         (~ (r2_hidden @ X2 @ k1_xboole_0)
% 20.85/21.05          | ~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 20.85/21.05      inference('sup-', [status(thm)], ['27', '30'])).
% 20.85/21.05  thf('32', plain,
% 20.85/21.05      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 20.85/21.05      inference('cnf', [status(esa)], [t79_xboole_1])).
% 20.85/21.05  thf('33', plain, (![X2 : $i]: ~ (r2_hidden @ X2 @ k1_xboole_0)),
% 20.85/21.05      inference('demod', [status(thm)], ['31', '32'])).
% 20.85/21.05  thf('34', plain, ($false), inference('sup-', [status(thm)], ['26', '33'])).
% 20.85/21.05  
% 20.85/21.05  % SZS output end Refutation
% 20.85/21.05  
% 20.85/21.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
