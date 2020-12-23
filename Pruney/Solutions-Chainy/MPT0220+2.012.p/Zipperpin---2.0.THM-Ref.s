%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tiUTssD3ti

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:20 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   68 (  83 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :   16
%              Number of atoms          :  434 ( 546 expanded)
%              Number of equality atoms :   53 (  67 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X50: $i,X51: $i] :
      ( r1_tarski @ ( k1_tarski @ X50 ) @ ( k2_tarski @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('24',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','32'])).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['5','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','41'])).

thf('43',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tiUTssD3ti
% 0.13/0.37  % Computer   : n011.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 12:51:27 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.44/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.68  % Solved by: fo/fo7.sh
% 0.44/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.68  % done 272 iterations in 0.201s
% 0.44/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.68  % SZS output start Refutation
% 0.44/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.68  thf(t14_zfmisc_1, conjecture,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.44/0.68       ( k2_tarski @ A @ B ) ))).
% 0.44/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.68    (~( ![A:$i,B:$i]:
% 0.44/0.68        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.44/0.68          ( k2_tarski @ A @ B ) ) )),
% 0.44/0.68    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.44/0.68  thf('0', plain,
% 0.44/0.68      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.44/0.68         != (k2_tarski @ sk_A @ sk_B))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(t12_zfmisc_1, axiom,
% 0.44/0.68    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.44/0.68  thf('1', plain,
% 0.44/0.68      (![X50 : $i, X51 : $i]:
% 0.44/0.68         (r1_tarski @ (k1_tarski @ X50) @ (k2_tarski @ X50 @ X51))),
% 0.44/0.68      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.44/0.68  thf(t28_xboole_1, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.68  thf('2', plain,
% 0.44/0.68      (![X12 : $i, X13 : $i]:
% 0.44/0.68         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.44/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.68  thf('3', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.44/0.68           = (k1_tarski @ X1))),
% 0.44/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.44/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.44/0.68  thf('4', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.68  thf(t48_xboole_1, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.68  thf('5', plain,
% 0.44/0.68      (![X15 : $i, X16 : $i]:
% 0.44/0.68         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.44/0.68           = (k3_xboole_0 @ X15 @ X16))),
% 0.44/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.68  thf(t100_xboole_1, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.68  thf('6', plain,
% 0.44/0.68      (![X10 : $i, X11 : $i]:
% 0.44/0.68         ((k4_xboole_0 @ X10 @ X11)
% 0.44/0.68           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.44/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.68  thf(commutativity_k5_xboole_0, axiom,
% 0.44/0.68    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.44/0.68  thf('7', plain,
% 0.44/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.44/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.44/0.68  thf(d10_xboole_0, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.68  thf('8', plain,
% 0.44/0.68      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.44/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.68  thf('9', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.44/0.68      inference('simplify', [status(thm)], ['8'])).
% 0.44/0.68  thf('10', plain,
% 0.44/0.68      (![X12 : $i, X13 : $i]:
% 0.44/0.68         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.44/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.68  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.44/0.68      inference('sup-', [status(thm)], ['9', '10'])).
% 0.44/0.68  thf('12', plain,
% 0.44/0.68      (![X10 : $i, X11 : $i]:
% 0.44/0.68         ((k4_xboole_0 @ X10 @ X11)
% 0.44/0.68           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.44/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.68  thf('13', plain,
% 0.44/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['11', '12'])).
% 0.44/0.68  thf('14', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.44/0.68      inference('simplify', [status(thm)], ['8'])).
% 0.44/0.68  thf(l32_xboole_1, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.68  thf('15', plain,
% 0.44/0.68      (![X7 : $i, X9 : $i]:
% 0.44/0.68         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.44/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.68  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.68  thf('17', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.68      inference('demod', [status(thm)], ['13', '16'])).
% 0.44/0.68  thf(t91_xboole_1, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i]:
% 0.44/0.68     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.44/0.68       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.44/0.68  thf('18', plain,
% 0.44/0.68      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.44/0.68           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.44/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.44/0.68  thf('19', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.44/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.44/0.68      inference('sup+', [status(thm)], ['17', '18'])).
% 0.44/0.68  thf(t3_boole, axiom,
% 0.44/0.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.68  thf('20', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.44/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.68  thf('21', plain,
% 0.44/0.68      (![X15 : $i, X16 : $i]:
% 0.44/0.68         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.44/0.68           = (k3_xboole_0 @ X15 @ X16))),
% 0.44/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.68  thf('22', plain,
% 0.44/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['20', '21'])).
% 0.44/0.68  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.68  thf('24', plain,
% 0.44/0.68      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.68      inference('demod', [status(thm)], ['22', '23'])).
% 0.44/0.68  thf('25', plain,
% 0.44/0.68      (![X10 : $i, X11 : $i]:
% 0.44/0.68         ((k4_xboole_0 @ X10 @ X11)
% 0.44/0.68           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.44/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.68  thf('26', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['24', '25'])).
% 0.44/0.68  thf('27', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.44/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.68  thf('28', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.44/0.68  thf('29', plain,
% 0.44/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.44/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.44/0.68  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['28', '29'])).
% 0.44/0.68  thf('31', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.44/0.68      inference('demod', [status(thm)], ['19', '30'])).
% 0.44/0.68  thf('32', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.44/0.68      inference('sup+', [status(thm)], ['7', '31'])).
% 0.44/0.68  thf('33', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((X1)
% 0.44/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.44/0.68      inference('sup+', [status(thm)], ['6', '32'])).
% 0.44/0.68  thf('34', plain,
% 0.44/0.68      (![X15 : $i, X16 : $i]:
% 0.44/0.68         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.44/0.68           = (k3_xboole_0 @ X15 @ X16))),
% 0.44/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.68  thf(t98_xboole_1, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.44/0.68  thf('35', plain,
% 0.44/0.68      (![X20 : $i, X21 : $i]:
% 0.44/0.68         ((k2_xboole_0 @ X20 @ X21)
% 0.44/0.68           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.44/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.44/0.68  thf('36', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.44/0.68           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.44/0.68      inference('sup+', [status(thm)], ['34', '35'])).
% 0.44/0.68  thf('37', plain,
% 0.44/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.44/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.44/0.68  thf('38', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.44/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.44/0.68      inference('demod', [status(thm)], ['36', '37'])).
% 0.44/0.68  thf('39', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['33', '38'])).
% 0.44/0.68  thf('40', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.44/0.68      inference('sup+', [status(thm)], ['5', '39'])).
% 0.44/0.68  thf('41', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['4', '40'])).
% 0.44/0.68  thf('42', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.44/0.68           = (k2_tarski @ X0 @ X1))),
% 0.44/0.68      inference('sup+', [status(thm)], ['3', '41'])).
% 0.44/0.68  thf('43', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['0', '42'])).
% 0.44/0.68  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.44/0.68  
% 0.44/0.68  % SZS output end Refutation
% 0.44/0.68  
% 0.44/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
