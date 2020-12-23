%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Z30HsTufY

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:19 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 131 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  460 ( 886 expanded)
%              Number of equality atoms :   53 ( 103 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X34: $i,X35: $i] :
      ( r1_tarski @ ( k1_tarski @ X34 ) @ ( k2_tarski @ X34 @ X35 ) ) ),
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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('25',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','25'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','43'])).

thf('45',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Z30HsTufY
% 0.15/0.37  % Computer   : n022.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 19:13:11 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.44/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.71  % Solved by: fo/fo7.sh
% 0.44/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.71  % done 529 iterations in 0.226s
% 0.44/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.71  % SZS output start Refutation
% 0.44/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.71  thf(t14_zfmisc_1, conjecture,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.44/0.71       ( k2_tarski @ A @ B ) ))).
% 0.44/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.71    (~( ![A:$i,B:$i]:
% 0.44/0.71        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.44/0.71          ( k2_tarski @ A @ B ) ) )),
% 0.44/0.71    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.44/0.71  thf('0', plain,
% 0.44/0.71      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.44/0.71         != (k2_tarski @ sk_A @ sk_B))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf(t12_zfmisc_1, axiom,
% 0.44/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.44/0.71  thf('1', plain,
% 0.44/0.71      (![X34 : $i, X35 : $i]:
% 0.44/0.71         (r1_tarski @ (k1_tarski @ X34) @ (k2_tarski @ X34 @ X35))),
% 0.44/0.71      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.44/0.71  thf(t28_xboole_1, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.71  thf('2', plain,
% 0.44/0.71      (![X12 : $i, X13 : $i]:
% 0.44/0.71         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.44/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.71  thf('3', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.44/0.71           = (k1_tarski @ X1))),
% 0.44/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.44/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.44/0.71  thf('4', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.71  thf(t36_xboole_1, axiom,
% 0.44/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.44/0.71  thf('5', plain,
% 0.44/0.71      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.44/0.71      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.71  thf('6', plain,
% 0.44/0.71      (![X12 : $i, X13 : $i]:
% 0.44/0.71         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.44/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.71  thf('7', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.44/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.44/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.71  thf('8', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.71  thf('9', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.44/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.44/0.71      inference('demod', [status(thm)], ['7', '8'])).
% 0.44/0.71  thf(t100_xboole_1, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.71  thf('10', plain,
% 0.44/0.71      (![X10 : $i, X11 : $i]:
% 0.44/0.71         ((k4_xboole_0 @ X10 @ X11)
% 0.44/0.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.44/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.71  thf('11', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.44/0.71           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.44/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.44/0.71  thf('12', plain,
% 0.44/0.71      (![X10 : $i, X11 : $i]:
% 0.44/0.71         ((k4_xboole_0 @ X10 @ X11)
% 0.44/0.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.44/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.71  thf(d10_xboole_0, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.71  thf('13', plain,
% 0.54/0.71      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.54/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.71  thf('14', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.54/0.71      inference('simplify', [status(thm)], ['13'])).
% 0.54/0.71  thf('15', plain,
% 0.54/0.71      (![X12 : $i, X13 : $i]:
% 0.54/0.71         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.54/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.54/0.71  thf('16', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.71  thf('17', plain,
% 0.54/0.71      (![X10 : $i, X11 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ X10 @ X11)
% 0.54/0.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.71  thf('18', plain,
% 0.54/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['16', '17'])).
% 0.54/0.71  thf(t79_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.54/0.71  thf('19', plain,
% 0.54/0.71      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.54/0.71      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.54/0.71  thf(d7_xboole_0, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.54/0.71       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.71  thf('20', plain,
% 0.54/0.71      (![X4 : $i, X5 : $i]:
% 0.54/0.71         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.54/0.71      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.54/0.71  thf('21', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.71  thf('22', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.71  thf('23', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.54/0.71      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.71  thf('24', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.54/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('demod', [status(thm)], ['7', '8'])).
% 0.54/0.71  thf('25', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['23', '24'])).
% 0.54/0.71  thf('26', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.71      inference('demod', [status(thm)], ['18', '25'])).
% 0.54/0.71  thf(t91_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.54/0.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.54/0.71  thf('27', plain,
% 0.54/0.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.54/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.54/0.71           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.54/0.71  thf('28', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.54/0.71           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['26', '27'])).
% 0.54/0.71  thf(commutativity_k5_xboole_0, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.54/0.71  thf('29', plain,
% 0.54/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.71  thf(t5_boole, axiom,
% 0.54/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.71  thf('30', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.54/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.71  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['29', '30'])).
% 0.54/0.71  thf('32', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('demod', [status(thm)], ['28', '31'])).
% 0.54/0.71  thf('33', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ X1 @ X0)
% 0.54/0.71           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['12', '32'])).
% 0.54/0.71  thf('34', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ X1 @ X0)
% 0.54/0.71           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['11', '33'])).
% 0.54/0.71  thf('35', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.54/0.71           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.54/0.71  thf('36', plain,
% 0.54/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.71  thf('37', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('demod', [status(thm)], ['28', '31'])).
% 0.54/0.71  thf('38', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['36', '37'])).
% 0.54/0.71  thf('39', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((X1)
% 0.54/0.71           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.54/0.71              (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.54/0.71      inference('sup+', [status(thm)], ['35', '38'])).
% 0.54/0.71  thf(t98_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.54/0.71  thf('40', plain,
% 0.54/0.71      (![X22 : $i, X23 : $i]:
% 0.54/0.71         ((k2_xboole_0 @ X22 @ X23)
% 0.54/0.71           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.54/0.71  thf('41', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((X1) = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.54/0.71      inference('demod', [status(thm)], ['39', '40'])).
% 0.54/0.71  thf('42', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((X1) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.54/0.71      inference('sup+', [status(thm)], ['34', '41'])).
% 0.54/0.71  thf('43', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['4', '42'])).
% 0.54/0.71  thf('44', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k2_tarski @ X0 @ X1)
% 0.54/0.71           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['3', '43'])).
% 0.54/0.71  thf('45', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.54/0.71      inference('demod', [status(thm)], ['0', '44'])).
% 0.54/0.71  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.54/0.71  
% 0.54/0.71  % SZS output end Refutation
% 0.54/0.71  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
