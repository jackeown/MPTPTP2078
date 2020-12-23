%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DHYfZLP96O

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:54 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   58 (  67 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  376 ( 462 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r2_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('6',plain,(
    ~ ( r2_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ~ ( r2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('21',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('23',plain,(
    ! [X47: $i,X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ ( k2_tarski @ X47 @ X50 ) )
      | ( X49
       != ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('24',plain,(
    ! [X47: $i,X50: $i] :
      ( r1_tarski @ ( k1_tarski @ X47 ) @ ( k2_tarski @ X47 @ X50 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','24'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X7 @ ( k2_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( r2_hidden @ X53 @ X54 )
      | ~ ( r1_tarski @ ( k2_tarski @ X53 @ X55 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['21','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DHYfZLP96O
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.14  % Solved by: fo/fo7.sh
% 0.90/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.14  % done 652 iterations in 0.694s
% 0.90/1.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.14  % SZS output start Refutation
% 0.90/1.14  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.90/1.14  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.14  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.90/1.14  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.14  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.14  thf(t45_zfmisc_1, conjecture,
% 0.90/1.14    (![A:$i,B:$i]:
% 0.90/1.14     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.90/1.14       ( r2_hidden @ A @ B ) ))).
% 0.90/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.14    (~( ![A:$i,B:$i]:
% 0.90/1.14        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.90/1.14          ( r2_hidden @ A @ B ) ) )),
% 0.90/1.14    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.90/1.14  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(t7_xboole_1, axiom,
% 0.90/1.14    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.90/1.14  thf('1', plain,
% 0.90/1.14      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 0.90/1.14      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.90/1.14  thf(d8_xboole_0, axiom,
% 0.90/1.14    (![A:$i,B:$i]:
% 0.90/1.14     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.90/1.14       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.90/1.14  thf('2', plain,
% 0.90/1.14      (![X4 : $i, X6 : $i]:
% 0.90/1.14         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.90/1.14      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.90/1.14  thf('3', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 0.90/1.14          | (r2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.14  thf('4', plain,
% 0.90/1.14      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(t60_xboole_1, axiom,
% 0.90/1.14    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.90/1.14  thf('5', plain,
% 0.90/1.14      (![X10 : $i, X11 : $i]:
% 0.90/1.14         (~ (r1_tarski @ X10 @ X11) | ~ (r2_xboole_0 @ X11 @ X10))),
% 0.90/1.14      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.90/1.14  thf('6', plain,
% 0.90/1.14      (~ (r2_xboole_0 @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.14  thf(t94_xboole_1, axiom,
% 0.90/1.14    (![A:$i,B:$i]:
% 0.90/1.14     ( ( k2_xboole_0 @ A @ B ) =
% 0.90/1.14       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.14  thf('7', plain,
% 0.90/1.14      (![X17 : $i, X18 : $i]:
% 0.90/1.14         ((k2_xboole_0 @ X17 @ X18)
% 0.90/1.14           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.90/1.14              (k3_xboole_0 @ X17 @ X18)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.90/1.14  thf(t91_xboole_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.90/1.14       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.90/1.14  thf('8', plain,
% 0.90/1.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.14         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.90/1.14           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.90/1.14  thf('9', plain,
% 0.90/1.14      (![X17 : $i, X18 : $i]:
% 0.90/1.14         ((k2_xboole_0 @ X17 @ X18)
% 0.90/1.14           = (k5_xboole_0 @ X17 @ 
% 0.90/1.14              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.90/1.14      inference('demod', [status(thm)], ['7', '8'])).
% 0.90/1.14  thf('10', plain,
% 0.90/1.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.14         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.90/1.14           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.90/1.14  thf(commutativity_k5_xboole_0, axiom,
% 0.90/1.14    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.90/1.14  thf('11', plain,
% 0.90/1.14      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.90/1.14      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.90/1.14  thf('12', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.90/1.14           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['10', '11'])).
% 0.90/1.14  thf('13', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k2_xboole_0 @ X1 @ X0)
% 0.90/1.14           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['9', '12'])).
% 0.90/1.14  thf('14', plain,
% 0.90/1.14      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.90/1.14      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.90/1.14  thf('15', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k2_xboole_0 @ X1 @ X0)
% 0.90/1.14           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.90/1.14      inference('demod', [status(thm)], ['13', '14'])).
% 0.90/1.14  thf(commutativity_k3_xboole_0, axiom,
% 0.90/1.14    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.90/1.14  thf('16', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.14  thf('17', plain,
% 0.90/1.14      (![X17 : $i, X18 : $i]:
% 0.90/1.14         ((k2_xboole_0 @ X17 @ X18)
% 0.90/1.14           = (k5_xboole_0 @ X17 @ 
% 0.90/1.14              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.90/1.14      inference('demod', [status(thm)], ['7', '8'])).
% 0.90/1.14  thf('18', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k2_xboole_0 @ X0 @ X1)
% 0.90/1.14           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.90/1.14      inference('sup+', [status(thm)], ['16', '17'])).
% 0.90/1.14  thf('19', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.90/1.14      inference('sup+', [status(thm)], ['15', '18'])).
% 0.90/1.14  thf('20', plain,
% 0.90/1.14      (~ (r2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.90/1.14      inference('demod', [status(thm)], ['6', '19'])).
% 0.90/1.14  thf('21', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['3', '20'])).
% 0.90/1.14  thf(t69_enumset1, axiom,
% 0.90/1.14    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.90/1.14  thf('22', plain,
% 0.90/1.14      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.90/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.14  thf(l45_zfmisc_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.90/1.14       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.90/1.14            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.90/1.14  thf('23', plain,
% 0.90/1.14      (![X47 : $i, X49 : $i, X50 : $i]:
% 0.90/1.14         ((r1_tarski @ X49 @ (k2_tarski @ X47 @ X50))
% 0.90/1.14          | ((X49) != (k1_tarski @ X47)))),
% 0.90/1.14      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.90/1.14  thf('24', plain,
% 0.90/1.14      (![X47 : $i, X50 : $i]:
% 0.90/1.14         (r1_tarski @ (k1_tarski @ X47) @ (k2_tarski @ X47 @ X50))),
% 0.90/1.14      inference('simplify', [status(thm)], ['23'])).
% 0.90/1.14  thf('25', plain,
% 0.90/1.14      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.90/1.14      inference('sup+', [status(thm)], ['22', '24'])).
% 0.90/1.14  thf(t10_xboole_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.90/1.14  thf('26', plain,
% 0.90/1.14      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.90/1.14         (~ (r1_tarski @ X7 @ X8) | (r1_tarski @ X7 @ (k2_xboole_0 @ X9 @ X8)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.90/1.14  thf('27', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (r1_tarski @ (k1_tarski @ X0) @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['25', '26'])).
% 0.90/1.14  thf('28', plain,
% 0.90/1.14      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.90/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.14  thf(t38_zfmisc_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.90/1.14       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.90/1.14  thf('29', plain,
% 0.90/1.14      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.90/1.14         ((r2_hidden @ X53 @ X54)
% 0.90/1.14          | ~ (r1_tarski @ (k2_tarski @ X53 @ X55) @ X54))),
% 0.90/1.14      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.90/1.14  thf('30', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.90/1.14      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.14  thf('31', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['27', '30'])).
% 0.90/1.14  thf('32', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.90/1.14      inference('sup+', [status(thm)], ['21', '31'])).
% 0.90/1.14  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.90/1.14  
% 0.90/1.14  % SZS output end Refutation
% 0.90/1.14  
% 0.90/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
