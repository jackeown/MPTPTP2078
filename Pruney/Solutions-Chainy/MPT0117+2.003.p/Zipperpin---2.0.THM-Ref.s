%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zKgrsBbIc4

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:47 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 115 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  407 ( 761 expanded)
%              Number of equality atoms :   47 (  81 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t110_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ B ) )
       => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t110_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['8','9','18'])).

thf(t99_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) @ ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['3','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('32',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['24','30','31','40'])).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zKgrsBbIc4
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:18 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 475 iterations in 0.331s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(t110_xboole_1, conjecture,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.59/0.78       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.59/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.78    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.78        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.59/0.78          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 0.59/0.78  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('1', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(l32_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.78  thf('2', plain,
% 0.59/0.78      (![X4 : $i, X6 : $i]:
% 0.59/0.78         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.59/0.78      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.78  thf('3', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.78  thf('4', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('5', plain,
% 0.59/0.78      (![X4 : $i, X6 : $i]:
% 0.59/0.78         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.59/0.78      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.78  thf('6', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.78  thf(t98_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.59/0.78  thf('7', plain,
% 0.59/0.78      (![X15 : $i, X16 : $i]:
% 0.59/0.78         ((k2_xboole_0 @ X15 @ X16)
% 0.59/0.78           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.59/0.78  thf('8', plain,
% 0.59/0.78      (((k2_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['6', '7'])).
% 0.59/0.78  thf(commutativity_k2_xboole_0, axiom,
% 0.59/0.78    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.59/0.78  thf('9', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.78  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.78    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.78  thf('10', plain,
% 0.59/0.78      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.59/0.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.78  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.59/0.78  thf('11', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.59/0.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.78  thf(t28_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.78  thf('12', plain,
% 0.59/0.78      (![X9 : $i, X10 : $i]:
% 0.59/0.78         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.59/0.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.78  thf('13', plain,
% 0.59/0.78      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.78  thf('14', plain,
% 0.59/0.78      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['10', '13'])).
% 0.59/0.78  thf(t100_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.78  thf('15', plain,
% 0.59/0.78      (![X7 : $i, X8 : $i]:
% 0.59/0.78         ((k4_xboole_0 @ X7 @ X8)
% 0.59/0.78           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.78  thf('16', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['14', '15'])).
% 0.59/0.78  thf(t3_boole, axiom,
% 0.59/0.78    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.78  thf('17', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.59/0.78      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.78  thf('18', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.78  thf('19', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.59/0.78      inference('demod', [status(thm)], ['8', '9', '18'])).
% 0.59/0.78  thf(t99_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.78       ( k2_xboole_0 @
% 0.59/0.78         ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ 
% 0.59/0.78         ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ))).
% 0.59/0.78  thf('20', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.78         ((k4_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.59/0.78           = (k2_xboole_0 @ (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)) @ 
% 0.59/0.78              (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X19))))),
% 0.59/0.78      inference('cnf', [status(esa)], [t99_xboole_1])).
% 0.59/0.78  thf('21', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k4_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.59/0.78           = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)) @ 
% 0.59/0.78              (k4_xboole_0 @ X0 @ sk_B)))),
% 0.59/0.78      inference('sup+', [status(thm)], ['19', '20'])).
% 0.59/0.78  thf('22', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.78  thf('23', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k4_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.59/0.78           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ 
% 0.59/0.78              (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B))))),
% 0.59/0.78      inference('demod', [status(thm)], ['21', '22'])).
% 0.59/0.78  thf('24', plain,
% 0.59/0.78      (((k4_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)
% 0.59/0.78         = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.59/0.78            (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))))),
% 0.59/0.78      inference('sup+', [status(thm)], ['3', '23'])).
% 0.59/0.78  thf('25', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.78  thf('26', plain,
% 0.59/0.78      (![X15 : $i, X16 : $i]:
% 0.59/0.78         ((k2_xboole_0 @ X15 @ X16)
% 0.59/0.78           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.59/0.78  thf('27', plain,
% 0.59/0.78      (((k2_xboole_0 @ sk_B @ sk_C) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['25', '26'])).
% 0.59/0.78  thf('28', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.78  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.78  thf('30', plain, (((k2_xboole_0 @ sk_C @ sk_B) = (sk_B))),
% 0.59/0.78      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.59/0.78  thf('31', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.78  thf('32', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.59/0.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.78  thf('33', plain,
% 0.59/0.78      (![X4 : $i, X6 : $i]:
% 0.59/0.78         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.59/0.78      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.78  thf('34', plain,
% 0.59/0.78      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.78  thf('35', plain,
% 0.59/0.78      (![X15 : $i, X16 : $i]:
% 0.59/0.78         ((k2_xboole_0 @ X15 @ X16)
% 0.59/0.78           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.59/0.78  thf('36', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['34', '35'])).
% 0.59/0.78  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.78  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['36', '37'])).
% 0.59/0.78  thf('39', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.78  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['38', '39'])).
% 0.59/0.78  thf('41', plain,
% 0.59/0.78      (((k4_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['24', '30', '31', '40'])).
% 0.59/0.78  thf('42', plain,
% 0.59/0.78      (![X4 : $i, X5 : $i]:
% 0.59/0.78         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.59/0.78      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.78  thf('43', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.78        | (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['41', '42'])).
% 0.59/0.78  thf('44', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.59/0.78      inference('simplify', [status(thm)], ['43'])).
% 0.59/0.78  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
