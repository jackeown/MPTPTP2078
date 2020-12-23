%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lFpb18GGNF

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:34 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   61 (  94 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  421 ( 744 expanded)
%              Number of equality atoms :   43 (  76 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t48_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != sk_B ),
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

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14','21','22'])).

thf('24',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X44: $i,X46: $i,X47: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X44 @ X46 ) @ X47 )
      | ~ ( r2_hidden @ X46 @ X47 )
      | ~ ( r2_hidden @ X44 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['24','27'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('32',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('38',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['0','23','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lFpb18GGNF
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:41:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.67/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.90  % Solved by: fo/fo7.sh
% 0.67/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.90  % done 259 iterations in 0.435s
% 0.67/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.90  % SZS output start Refutation
% 0.67/0.90  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.67/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.67/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.90  thf(t48_zfmisc_1, conjecture,
% 0.67/0.90    (![A:$i,B:$i,C:$i]:
% 0.67/0.90     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.67/0.90       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.67/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.90    (~( ![A:$i,B:$i,C:$i]:
% 0.67/0.90        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.67/0.90          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.67/0.90    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.67/0.90  thf('0', plain,
% 0.67/0.90      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) != (sk_B))),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf(commutativity_k3_xboole_0, axiom,
% 0.67/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.67/0.90  thf('1', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.67/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.67/0.90  thf(t100_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.67/0.90  thf('2', plain,
% 0.67/0.90      (![X7 : $i, X8 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ X7 @ X8)
% 0.67/0.90           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.90  thf('3', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ X0 @ X1)
% 0.67/0.90           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['1', '2'])).
% 0.67/0.90  thf('4', plain,
% 0.67/0.90      (![X7 : $i, X8 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ X7 @ X8)
% 0.67/0.90           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.90  thf(commutativity_k5_xboole_0, axiom,
% 0.67/0.90    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.67/0.90  thf('5', plain,
% 0.67/0.90      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.67/0.90      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.67/0.90  thf(t91_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i,C:$i]:
% 0.67/0.90     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.67/0.90       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.67/0.90  thf('6', plain,
% 0.67/0.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.67/0.90         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.67/0.90           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.67/0.90  thf('7', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.90         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.67/0.90           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['5', '6'])).
% 0.67/0.90  thf('8', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.90         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.67/0.90           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X2)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['4', '7'])).
% 0.67/0.90  thf('9', plain,
% 0.67/0.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.67/0.90         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.67/0.90           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.67/0.90  thf('10', plain,
% 0.67/0.90      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.67/0.90      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.67/0.90  thf('11', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.90         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.67/0.90           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['9', '10'])).
% 0.67/0.90  thf('12', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.90         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.67/0.90           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.67/0.90      inference('demod', [status(thm)], ['8', '11'])).
% 0.67/0.90  thf('13', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 0.67/0.90           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['3', '12'])).
% 0.67/0.90  thf('14', plain,
% 0.67/0.90      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.67/0.90      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.67/0.90  thf('15', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.67/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.67/0.90  thf(t94_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( k2_xboole_0 @ A @ B ) =
% 0.67/0.90       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.67/0.90  thf('16', plain,
% 0.67/0.90      (![X13 : $i, X14 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ X13 @ X14)
% 0.67/0.90           = (k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 0.67/0.90              (k3_xboole_0 @ X13 @ X14)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.67/0.90  thf('17', plain,
% 0.67/0.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.67/0.90         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.67/0.90           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.67/0.90  thf('18', plain,
% 0.67/0.90      (![X13 : $i, X14 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ X13 @ X14)
% 0.67/0.90           = (k5_xboole_0 @ X13 @ 
% 0.67/0.90              (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X13 @ X14))))),
% 0.67/0.90      inference('demod', [status(thm)], ['16', '17'])).
% 0.67/0.90  thf('19', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ X0 @ X1)
% 0.67/0.90           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.67/0.90      inference('sup+', [status(thm)], ['15', '18'])).
% 0.67/0.90  thf('20', plain,
% 0.67/0.90      (![X7 : $i, X8 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ X7 @ X8)
% 0.67/0.90           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.90  thf('21', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ X0 @ X1)
% 0.67/0.90           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.90      inference('demod', [status(thm)], ['19', '20'])).
% 0.67/0.90  thf('22', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ X0 @ X1)
% 0.67/0.90           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.90      inference('demod', [status(thm)], ['19', '20'])).
% 0.67/0.90  thf('23', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.90      inference('demod', [status(thm)], ['13', '14', '21', '22'])).
% 0.67/0.90  thf('24', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('25', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf(t38_zfmisc_1, axiom,
% 0.67/0.90    (![A:$i,B:$i,C:$i]:
% 0.67/0.90     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.67/0.90       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.67/0.90  thf('26', plain,
% 0.67/0.90      (![X44 : $i, X46 : $i, X47 : $i]:
% 0.67/0.90         ((r1_tarski @ (k2_tarski @ X44 @ X46) @ X47)
% 0.67/0.90          | ~ (r2_hidden @ X46 @ X47)
% 0.67/0.90          | ~ (r2_hidden @ X44 @ X47))),
% 0.67/0.90      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.67/0.90  thf('27', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (~ (r2_hidden @ X0 @ sk_B)
% 0.67/0.90          | (r1_tarski @ (k2_tarski @ X0 @ sk_C) @ sk_B))),
% 0.67/0.90      inference('sup-', [status(thm)], ['25', '26'])).
% 0.67/0.90  thf('28', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.67/0.90      inference('sup-', [status(thm)], ['24', '27'])).
% 0.67/0.90  thf(l32_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.90  thf('29', plain,
% 0.67/0.90      (![X4 : $i, X6 : $i]:
% 0.67/0.90         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.67/0.90      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.67/0.90  thf('30', plain,
% 0.67/0.90      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['28', '29'])).
% 0.67/0.90  thf('31', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ X0 @ X1)
% 0.67/0.90           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.90      inference('demod', [status(thm)], ['19', '20'])).
% 0.67/0.90  thf('32', plain,
% 0.67/0.90      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))
% 0.67/0.90         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.67/0.90      inference('sup+', [status(thm)], ['30', '31'])).
% 0.67/0.90  thf('33', plain,
% 0.67/0.90      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.67/0.90      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.67/0.90  thf('34', plain,
% 0.67/0.90      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.67/0.90      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.67/0.90  thf(t5_boole, axiom,
% 0.67/0.90    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.67/0.90  thf('35', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.67/0.90      inference('cnf', [status(esa)], [t5_boole])).
% 0.67/0.90  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.67/0.90      inference('sup+', [status(thm)], ['34', '35'])).
% 0.67/0.90  thf('37', plain,
% 0.67/0.90      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)) = (sk_B))),
% 0.67/0.90      inference('demod', [status(thm)], ['32', '33', '36'])).
% 0.67/0.90  thf('38', plain, (((sk_B) != (sk_B))),
% 0.67/0.90      inference('demod', [status(thm)], ['0', '23', '37'])).
% 0.67/0.90  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 0.67/0.90  
% 0.67/0.90  % SZS output end Refutation
% 0.67/0.90  
% 0.67/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
