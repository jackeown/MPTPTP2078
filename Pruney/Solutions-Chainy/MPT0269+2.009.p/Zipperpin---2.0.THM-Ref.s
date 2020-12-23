%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gy5qqT4po8

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:03 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   65 (  72 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  353 ( 436 expanded)
%              Number of equality atoms :   38 (  57 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t105_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ( ( k4_xboole_0 @ B @ A )
          = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_xboole_0 @ X17 @ X18 )
      | ( ( k4_xboole_0 @ X18 @ X17 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t105_xboole_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( r2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( r2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X55 ) @ X56 )
      | ( r2_hidden @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['16','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
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

thf('20',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B_1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','23'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['24','28'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('30',plain,(
    ! [X52: $i,X54: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X52 ) @ X54 )
      | ~ ( r2_hidden @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('31',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_xboole_0 @ X7 @ X9 )
      | ( X7 = X9 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('33',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ( r2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['3','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gy5qqT4po8
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 237 iterations in 0.119s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.36/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.57  thf(t66_zfmisc_1, conjecture,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.36/0.57          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i,B:$i]:
% 0.36/0.57        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.36/0.57             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.36/0.57  thf('0', plain,
% 0.36/0.57      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t105_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.36/0.57          ( ( k4_xboole_0 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      (![X17 : $i, X18 : $i]:
% 0.36/0.57         (~ (r2_xboole_0 @ X17 @ X18)
% 0.36/0.57          | ((k4_xboole_0 @ X18 @ X17) != (k1_xboole_0)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t105_xboole_1])).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.57        | ~ (r2_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.57  thf('3', plain, (~ (r2_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.36/0.57      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.57  thf(d1_xboole_0, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.57  thf('4', plain,
% 0.36/0.57      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.36/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.57  thf(l27_zfmisc_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      (![X55 : $i, X56 : $i]:
% 0.36/0.57         ((r1_xboole_0 @ (k1_tarski @ X55) @ X56) | (r2_hidden @ X55 @ X56))),
% 0.36/0.57      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.36/0.57  thf('6', plain,
% 0.36/0.57      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t100_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.57  thf('7', plain,
% 0.36/0.57      (![X15 : $i, X16 : $i]:
% 0.36/0.57         ((k4_xboole_0 @ X15 @ X16)
% 0.36/0.57           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.57  thf(t92_xboole_1, axiom,
% 0.36/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.57  thf('8', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.57  thf(t91_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.57       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.36/0.57  thf('9', plain,
% 0.36/0.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.36/0.57           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.57  thf('10', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.57           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.57  thf(commutativity_k5_xboole_0, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.36/0.57  thf('11', plain,
% 0.36/0.57      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.36/0.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.36/0.57  thf(t5_boole, axiom,
% 0.36/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.57  thf('12', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.36/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.57  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.36/0.57  thf('14', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.57      inference('demod', [status(thm)], ['10', '13'])).
% 0.36/0.57  thf('15', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k3_xboole_0 @ X1 @ X0)
% 0.36/0.57           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['7', '14'])).
% 0.36/0.57  thf('16', plain,
% 0.36/0.57      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.36/0.57         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.36/0.57      inference('sup+', [status(thm)], ['6', '15'])).
% 0.36/0.57  thf('17', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.36/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.57  thf('18', plain, (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.36/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.57  thf('19', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.57  thf(t4_xboole_0, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.36/0.57            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 0.36/0.57          | ~ (r1_xboole_0 @ X11 @ X14))),
% 0.36/0.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.36/0.57  thf('21', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.36/0.57          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.57  thf('22', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.57          | ~ (r1_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['18', '21'])).
% 0.36/0.57  thf('23', plain,
% 0.36/0.57      (![X0 : $i]: ((r2_hidden @ sk_B_1 @ sk_A) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['5', '22'])).
% 0.36/0.57  thf('24', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['4', '23'])).
% 0.36/0.57  thf(l13_xboole_0, axiom,
% 0.36/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.57  thf('25', plain,
% 0.36/0.57      (![X10 : $i]: (((X10) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X10))),
% 0.36/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.57  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('27', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.57  thf('28', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.36/0.57      inference('simplify', [status(thm)], ['27'])).
% 0.36/0.57  thf('29', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.36/0.57      inference('clc', [status(thm)], ['24', '28'])).
% 0.36/0.57  thf(l1_zfmisc_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.36/0.57  thf('30', plain,
% 0.36/0.57      (![X52 : $i, X54 : $i]:
% 0.36/0.57         ((r1_tarski @ (k1_tarski @ X52) @ X54) | ~ (r2_hidden @ X52 @ X54))),
% 0.36/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.36/0.57  thf('31', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.36/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.57  thf(d8_xboole_0, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.36/0.57       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.36/0.57  thf('32', plain,
% 0.36/0.57      (![X7 : $i, X9 : $i]:
% 0.36/0.57         ((r2_xboole_0 @ X7 @ X9) | ((X7) = (X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.36/0.57      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.36/0.57  thf('33', plain,
% 0.36/0.57      ((((k1_tarski @ sk_B_1) = (sk_A))
% 0.36/0.57        | (r2_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.57  thf('34', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('35', plain, ((r2_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.36/0.57      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.36/0.57  thf('36', plain, ($false), inference('demod', [status(thm)], ['3', '35'])).
% 0.36/0.57  
% 0.36/0.57  % SZS output end Refutation
% 0.36/0.57  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
