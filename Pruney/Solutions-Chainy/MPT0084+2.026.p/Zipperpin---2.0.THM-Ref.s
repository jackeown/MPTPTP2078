%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JC46ZIxtVl

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:22 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   63 (  82 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :  407 ( 570 expanded)
%              Number of equality atoms :   45 (  60 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ X0 ) ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ X0 ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ sk_A ) ),
    inference('sup+',[status(thm)],['6','26'])).

thf('28',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup+',[status(thm)],['5','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('30',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JC46ZIxtVl
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:14:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 367 iterations in 0.148s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(t77_xboole_1, conjecture,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.37/0.61          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.61        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.37/0.61             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.37/0.61  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('1', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t28_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (![X5 : $i, X6 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.61  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf('5', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['3', '4'])).
% 0.37/0.61  thf(t48_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.37/0.61           = (k3_xboole_0 @ X11 @ X12))),
% 0.37/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.61  thf('7', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(d7_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      (![X2 : $i, X3 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.37/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.61  thf(t49_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.37/0.61       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.61         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.37/0.61           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.37/0.61      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k3_xboole_0 @ sk_A @ 
% 0.37/0.61           (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.37/0.61           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['9', '10'])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.61         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.37/0.61           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.37/0.61      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k3_xboole_0 @ sk_A @ 
% 0.37/0.61           (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ X0)))
% 0.37/0.61           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf(t2_boole, axiom,
% 0.37/0.61    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.61  thf(t47_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.37/0.61           = (k4_xboole_0 @ X9 @ X10))),
% 0.37/0.61      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.37/0.61           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['16', '17'])).
% 0.37/0.61  thf(t3_boole, axiom,
% 0.37/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.61  thf('19', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.61  thf('20', plain,
% 0.37/0.61      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k3_xboole_0 @ sk_A @ 
% 0.37/0.61           (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ X0))) = (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['13', '20'])).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      (![X2 : $i, X4 : $i]:
% 0.37/0.61         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.61          | (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ X0)) @ 
% 0.37/0.61             sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['21', '24'])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ X0)) @ sk_A)),
% 0.37/0.61      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)) @ sk_A)),
% 0.37/0.61      inference('sup+', [status(thm)], ['6', '26'])).
% 0.37/0.61  thf('28', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_A)),
% 0.37/0.61      inference('sup+', [status(thm)], ['5', '27'])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      (![X2 : $i, X3 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.37/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_A) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf('32', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf('33', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.37/0.61           = (k4_xboole_0 @ X9 @ X10))),
% 0.37/0.61      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.61           = (k4_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['32', '33'])).
% 0.37/0.61  thf('35', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.37/0.61           = (k3_xboole_0 @ X11 @ X12))),
% 0.37/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.61  thf('36', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.37/0.61           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['34', '35'])).
% 0.37/0.61  thf('37', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.37/0.61           = (k3_xboole_0 @ X11 @ X12))),
% 0.37/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k3_xboole_0 @ X1 @ X0)
% 0.37/0.61           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.61      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.61  thf('39', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf('40', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['30', '31', '38', '39'])).
% 0.37/0.61  thf('41', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.61  thf('43', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.37/0.61      inference('simplify', [status(thm)], ['42'])).
% 0.37/0.61  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
