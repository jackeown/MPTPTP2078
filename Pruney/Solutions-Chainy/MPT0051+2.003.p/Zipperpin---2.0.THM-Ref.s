%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dosbsMH6vz

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:05 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 100 expanded)
%              Number of leaves         :   13 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  417 ( 714 expanded)
%              Number of equality atoms :   37 (  57 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t44_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
       => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ sk_C )
      = ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_C )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','32'])).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('44',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['2','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dosbsMH6vz
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:34:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.63  % Solved by: fo/fo7.sh
% 0.37/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.63  % done 307 iterations in 0.174s
% 0.37/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.63  % SZS output start Refutation
% 0.37/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.63  thf(t44_xboole_1, conjecture,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.37/0.63       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.63        ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.37/0.63          ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )),
% 0.37/0.63    inference('cnf.neg', [status(esa)], [t44_xboole_1])).
% 0.37/0.63  thf('0', plain, (~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(commutativity_k2_xboole_0, axiom,
% 0.37/0.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.37/0.63  thf('1', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.63  thf('2', plain, (~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))),
% 0.37/0.63      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.63  thf(t7_xboole_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.63  thf('3', plain,
% 0.37/0.63      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 0.37/0.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.63  thf(t43_xboole_1, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.37/0.63       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.37/0.63  thf('4', plain,
% 0.37/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.63         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.37/0.63          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.37/0.63      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.37/0.63  thf('5', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.37/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.63  thf(t12_xboole_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.37/0.63  thf('6', plain,
% 0.37/0.63      (![X2 : $i, X3 : $i]:
% 0.37/0.63         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.37/0.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.63  thf('7', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.63  thf('8', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.63  thf('9', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1)) = (X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.63  thf('10', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.63  thf('11', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))),
% 0.37/0.63      inference('sup+', [status(thm)], ['9', '10'])).
% 0.37/0.63  thf('12', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('13', plain,
% 0.37/0.63      (![X2 : $i, X3 : $i]:
% 0.37/0.63         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.37/0.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.63  thf('14', plain,
% 0.37/0.63      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C) = (sk_C))),
% 0.37/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.63  thf('15', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.63  thf('16', plain,
% 0.37/0.63      (((k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_C))),
% 0.37/0.63      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.63  thf('17', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.63  thf(t41_xboole_1, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.63       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.63  thf('18', plain,
% 0.37/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.37/0.63           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.37/0.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.37/0.63  thf('19', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.37/0.63           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.63      inference('sup+', [status(thm)], ['17', '18'])).
% 0.37/0.63  thf('20', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 0.37/0.63           sk_C) = (k4_xboole_0 @ X0 @ sk_C))),
% 0.37/0.63      inference('sup+', [status(thm)], ['16', '19'])).
% 0.37/0.63  thf('21', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ sk_C)
% 0.37/0.63           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.37/0.63      inference('sup+', [status(thm)], ['11', '20'])).
% 0.37/0.63  thf('22', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.63  thf('23', plain,
% 0.37/0.63      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 0.37/0.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.63  thf('24', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.63  thf('25', plain,
% 0.37/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.63         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.37/0.63          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.37/0.63      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.37/0.63  thf('26', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.37/0.63      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.63  thf('27', plain,
% 0.37/0.63      (![X2 : $i, X3 : $i]:
% 0.37/0.63         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.37/0.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.63  thf('28', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.63  thf('29', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.63  thf('30', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.37/0.63      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.63  thf('31', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.63  thf('32', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X0 @ X0)
% 0.37/0.63           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.37/0.63      inference('sup+', [status(thm)], ['30', '31'])).
% 0.37/0.63  thf('33', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X0 @ X0)
% 0.37/0.63           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.37/0.63      inference('demod', [status(thm)], ['21', '32'])).
% 0.37/0.63  thf('34', plain,
% 0.37/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.37/0.63           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.37/0.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.37/0.63  thf(t39_xboole_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.63  thf('35', plain,
% 0.37/0.63      (![X4 : $i, X5 : $i]:
% 0.37/0.63         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.37/0.63           = (k2_xboole_0 @ X4 @ X5))),
% 0.37/0.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.63  thf('36', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.63         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.37/0.63           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.37/0.63           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.37/0.63      inference('sup+', [status(thm)], ['34', '35'])).
% 0.37/0.63  thf('37', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((k2_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ (k4_xboole_0 @ X0 @ X0))
% 0.37/0.63           = (k2_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.37/0.63      inference('sup+', [status(thm)], ['33', '36'])).
% 0.37/0.63  thf('38', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.63  thf('39', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1)) = (X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.63  thf('40', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.63  thf('41', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.63  thf('42', plain,
% 0.37/0.63      (((k2_xboole_0 @ sk_C @ sk_B)
% 0.37/0.63         = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 0.37/0.63      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.37/0.63  thf('43', plain,
% 0.37/0.63      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 0.37/0.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.63  thf('44', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))),
% 0.37/0.63      inference('sup+', [status(thm)], ['42', '43'])).
% 0.37/0.63  thf('45', plain, ($false), inference('demod', [status(thm)], ['2', '44'])).
% 0.37/0.63  
% 0.37/0.63  % SZS output end Refutation
% 0.37/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
