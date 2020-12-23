%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0jbMpAC9im

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:21 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   66 (  82 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  431 ( 543 expanded)
%              Number of equality atoms :   50 (  64 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t14_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t14_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X48: $i,X49: $i] :
      ( r1_tarski @ ( k1_tarski @ X48 ) @ ( k2_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16','21','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['5','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','39'])).

thf('41',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0jbMpAC9im
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:34:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 422 iterations in 0.191s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(t14_zfmisc_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.46/0.64       ( k2_tarski @ A @ B ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i]:
% 0.46/0.64        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.46/0.64          ( k2_tarski @ A @ B ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.46/0.64         != (k2_tarski @ sk_A @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t12_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X48 : $i, X49 : $i]:
% 0.46/0.64         (r1_tarski @ (k1_tarski @ X48) @ (k2_tarski @ X48 @ X49))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.46/0.64  thf(t28_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.46/0.64           = (k1_tarski @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf(t48_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.46/0.64           = (k3_xboole_0 @ X13 @ X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf(d10_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('7', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.46/0.64      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.64  thf('9', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf(t100_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X7 @ X8)
% 0.46/0.64           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['9', '10'])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X7 @ X8)
% 0.46/0.64           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf(t91_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.64       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.46/0.64           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.46/0.64           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.64           = (k5_xboole_0 @ X1 @ 
% 0.46/0.64              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['11', '14'])).
% 0.46/0.64  thf(commutativity_k5_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.46/0.64           = (k3_xboole_0 @ X13 @ X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf(t98_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X18 @ X19)
% 0.46/0.64           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.64           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.64           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf(t3_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.64  thf('22', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.46/0.64           = (k3_xboole_0 @ X13 @ X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['22', '23'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.64  thf('26', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['25', '28'])).
% 0.46/0.64  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['24', '29'])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.64           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['15', '16', '21', '30'])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['25', '28'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X7 @ X8)
% 0.46/0.64           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['32', '33'])).
% 0.46/0.64  thf('35', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.64  thf('36', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.46/0.64      inference('demod', [status(thm)], ['31', '36'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['5', '37'])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['4', '38'])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.46/0.64           = (k2_tarski @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['3', '39'])).
% 0.46/0.64  thf('41', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['0', '40'])).
% 0.46/0.64  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.48/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
