%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qpd0rBynTe

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 148 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  472 (1085 expanded)
%              Number of equality atoms :   39 (  73 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t47_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t47_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    | ( sk_C
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( r2_hidden @ X73 @ X72 )
      | ~ ( r1_tarski @ ( k2_tarski @ X71 @ X73 ) @ X72 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('9',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ ( k2_tarski @ X71 @ X73 ) @ X72 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X71: $i,X73: $i,X74: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X71 @ X73 ) @ X74 )
      | ~ ( r2_hidden @ X73 @ X74 )
      | ~ ( r2_hidden @ X71 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X69: $i,X70: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X69 @ X70 ) )
      = ( k2_xboole_0 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X69: $i,X70: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X69 @ X70 ) )
      = ( k2_xboole_0 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('24',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','21','22','23'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('33',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('36',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('37',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','41'])).

thf('43',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k2_xboole_0 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ ( k2_tarski @ X71 @ X73 ) @ X72 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('48',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qpd0rBynTe
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.56  % Solved by: fo/fo7.sh
% 0.22/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.56  % done 157 iterations in 0.099s
% 0.22/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.56  % SZS output start Refutation
% 0.22/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.56  thf(t47_zfmisc_1, conjecture,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.22/0.56       ( r2_hidden @ A @ C ) ))).
% 0.22/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.57        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.22/0.57          ( r2_hidden @ A @ C ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.22/0.57  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(d10_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (![X4 : $i, X6 : $i]:
% 0.22/0.57         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.22/0.57        | ((sk_C) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.57  thf('5', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.22/0.57      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.57  thf(t38_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.22/0.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (![X71 : $i, X72 : $i, X73 : $i]:
% 0.22/0.57         ((r2_hidden @ X73 @ X72)
% 0.22/0.57          | ~ (r1_tarski @ (k2_tarski @ X71 @ X73) @ X72))),
% 0.22/0.57      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.57  thf('8', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.22/0.57      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      (![X71 : $i, X72 : $i, X73 : $i]:
% 0.22/0.57         ((r2_hidden @ X71 @ X72)
% 0.22/0.57          | ~ (r1_tarski @ (k2_tarski @ X71 @ X73) @ X72))),
% 0.22/0.57      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.57  thf('10', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.57  thf('11', plain,
% 0.22/0.57      (![X71 : $i, X73 : $i, X74 : $i]:
% 0.22/0.57         ((r1_tarski @ (k2_tarski @ X71 @ X73) @ X74)
% 0.22/0.57          | ~ (r2_hidden @ X73 @ X74)
% 0.22/0.57          | ~ (r2_hidden @ X71 @ X74))),
% 0.22/0.57      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.57          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.57  thf('13', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['7', '12'])).
% 0.22/0.57  thf('14', plain,
% 0.22/0.57      (![X4 : $i, X6 : $i]:
% 0.22/0.57         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 0.22/0.57          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['7', '12'])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.22/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.57  thf(l51_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      (![X69 : $i, X70 : $i]:
% 0.22/0.57         ((k3_tarski @ (k2_tarski @ X69 @ X70)) = (k2_xboole_0 @ X69 @ X70))),
% 0.22/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.22/0.57  thf('20', plain,
% 0.22/0.57      (![X69 : $i, X70 : $i]:
% 0.22/0.57         ((k3_tarski @ (k2_tarski @ X69 @ X70)) = (k2_xboole_0 @ X69 @ X70))),
% 0.22/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.57  thf(t7_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.22/0.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.57  thf('23', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.22/0.57      inference('demod', [status(thm)], ['3', '21', '22', '23'])).
% 0.22/0.57  thf(t95_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k3_xboole_0 @ A @ B ) =
% 0.22/0.57       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.22/0.57  thf('25', plain,
% 0.22/0.57      (![X16 : $i, X17 : $i]:
% 0.22/0.57         ((k3_xboole_0 @ X16 @ X17)
% 0.22/0.57           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.22/0.57              (k2_xboole_0 @ X16 @ X17)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.22/0.57  thf(t91_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.57       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.22/0.57  thf('26', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.22/0.57           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.57  thf('27', plain,
% 0.22/0.57      (![X16 : $i, X17 : $i]:
% 0.22/0.57         ((k3_xboole_0 @ X16 @ X17)
% 0.22/0.57           = (k5_xboole_0 @ X16 @ 
% 0.22/0.57              (k5_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X17))))),
% 0.22/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.22/0.57         = (k5_xboole_0 @ sk_C @ 
% 0.22/0.57            (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['24', '27'])).
% 0.22/0.57  thf(commutativity_k5_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.57  thf(t92_xboole_1, axiom,
% 0.22/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.57  thf('30', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.22/0.57           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.57           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['30', '31'])).
% 0.22/0.57  thf(idempotence_k2_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.57  thf('33', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.22/0.57      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (![X16 : $i, X17 : $i]:
% 0.22/0.57         ((k3_xboole_0 @ X16 @ X17)
% 0.22/0.57           = (k5_xboole_0 @ X16 @ 
% 0.22/0.57              (k5_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X17))))),
% 0.22/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((k3_xboole_0 @ X0 @ X0)
% 0.22/0.57           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['33', '34'])).
% 0.22/0.57  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.57  thf('36', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.22/0.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.57  thf('37', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.57  thf('38', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.57      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.22/0.57  thf('39', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.57  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.57      inference('sup+', [status(thm)], ['38', '39'])).
% 0.22/0.57  thf('41', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['32', '40'])).
% 0.22/0.57  thf('42', plain,
% 0.22/0.57      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.22/0.57         = (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.57      inference('demod', [status(thm)], ['28', '29', '41'])).
% 0.22/0.57  thf('43', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.22/0.57      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.22/0.57  thf(t29_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 0.22/0.57  thf('44', plain,
% 0.22/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.57         (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ (k2_xboole_0 @ X7 @ X9))),
% 0.22/0.57      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.22/0.57  thf('45', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.57      inference('sup+', [status(thm)], ['43', '44'])).
% 0.22/0.57  thf('46', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.22/0.57      inference('sup+', [status(thm)], ['42', '45'])).
% 0.22/0.57  thf('47', plain,
% 0.22/0.57      (![X71 : $i, X72 : $i, X73 : $i]:
% 0.22/0.57         ((r2_hidden @ X71 @ X72)
% 0.22/0.57          | ~ (r1_tarski @ (k2_tarski @ X71 @ X73) @ X72))),
% 0.22/0.57      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.57  thf('48', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.22/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.57  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
