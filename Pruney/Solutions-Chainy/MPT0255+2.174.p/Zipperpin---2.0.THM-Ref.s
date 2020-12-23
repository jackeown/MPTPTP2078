%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OFejFWbz2q

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:16 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 123 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :   20
%              Number of atoms          :  448 ( 778 expanded)
%              Number of equality atoms :   71 ( 131 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['2'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X69: $i,X70: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X69 @ X70 ) )
      = ( k2_xboole_0 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('7',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('8',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('10',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( k2_tarski @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','11'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('14',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('15',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('16',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','24'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('30',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','28','29'])).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('34',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('39',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('41',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','40','41'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('43',plain,(
    ! [X71: $i,X72: $i] :
      ( ( X72 != X71 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X72 ) @ ( k1_tarski @ X71 ) )
       != ( k1_tarski @ X72 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('44',plain,(
    ! [X71: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X71 ) @ ( k1_tarski @ X71 ) )
     != ( k1_tarski @ X71 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('46',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X71: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X71 ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    $false ),
    inference(simplify,[status(thm)],['49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OFejFWbz2q
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:47:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.57  % Solved by: fo/fo7.sh
% 0.41/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.57  % done 278 iterations in 0.113s
% 0.41/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.57  % SZS output start Refutation
% 0.41/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.41/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.41/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.57  thf(t50_zfmisc_1, conjecture,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.41/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.57        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.41/0.57    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.41/0.57  thf('0', plain,
% 0.41/0.57      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(t15_xboole_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.57       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.57  thf('1', plain,
% 0.41/0.57      (![X4 : $i, X5 : $i]:
% 0.41/0.57         (((X4) = (k1_xboole_0)) | ((k2_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.41/0.57      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.41/0.57  thf('2', plain,
% 0.41/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.57  thf('3', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.41/0.57      inference('simplify', [status(thm)], ['2'])).
% 0.41/0.57  thf('4', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.41/0.57      inference('simplify', [status(thm)], ['2'])).
% 0.41/0.57  thf(l51_zfmisc_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.57  thf('5', plain,
% 0.41/0.57      (![X69 : $i, X70 : $i]:
% 0.41/0.57         ((k3_tarski @ (k2_tarski @ X69 @ X70)) = (k2_xboole_0 @ X69 @ X70))),
% 0.41/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.41/0.57  thf('6', plain, (((k3_tarski @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.57  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.41/0.57  thf('7', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.57      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.41/0.57  thf('8', plain, (((k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.41/0.57  thf('9', plain,
% 0.41/0.57      (![X4 : $i, X5 : $i]:
% 0.41/0.57         (((X4) = (k1_xboole_0)) | ((k2_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.41/0.57      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.41/0.57  thf('10', plain,
% 0.41/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.57  thf('11', plain, (((sk_A) = (k1_xboole_0))),
% 0.41/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.41/0.57  thf('12', plain, (((k2_tarski @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.41/0.57      inference('demod', [status(thm)], ['3', '11'])).
% 0.41/0.57  thf(t92_xboole_1, axiom,
% 0.41/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.41/0.57  thf('13', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.41/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.41/0.57  thf('14', plain, (((k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.41/0.57  thf('15', plain, (((sk_A) = (k1_xboole_0))),
% 0.41/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.41/0.57  thf('16', plain, (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.41/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.57  thf(t95_xboole_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( k3_xboole_0 @ A @ B ) =
% 0.41/0.57       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.41/0.57  thf('17', plain,
% 0.41/0.57      (![X12 : $i, X13 : $i]:
% 0.41/0.57         ((k3_xboole_0 @ X12 @ X13)
% 0.41/0.57           = (k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ 
% 0.41/0.57              (k2_xboole_0 @ X12 @ X13)))),
% 0.41/0.57      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.41/0.57  thf(t91_xboole_1, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.41/0.57       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.41/0.57  thf('18', plain,
% 0.41/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.41/0.57           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.41/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.41/0.57  thf('19', plain,
% 0.41/0.57      (![X12 : $i, X13 : $i]:
% 0.41/0.57         ((k3_xboole_0 @ X12 @ X13)
% 0.41/0.57           = (k5_xboole_0 @ X12 @ 
% 0.41/0.57              (k5_xboole_0 @ X13 @ (k2_xboole_0 @ X12 @ X13))))),
% 0.41/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.41/0.57  thf('20', plain,
% 0.41/0.57      (((k3_xboole_0 @ k1_xboole_0 @ sk_B)
% 0.41/0.57         = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ sk_B @ k1_xboole_0)))),
% 0.41/0.57      inference('sup+', [status(thm)], ['16', '19'])).
% 0.41/0.57  thf(t5_boole, axiom,
% 0.41/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.57  thf('21', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.41/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.57  thf('22', plain,
% 0.41/0.57      (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k5_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.41/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.41/0.57  thf('23', plain,
% 0.41/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.41/0.57           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.41/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.41/0.57  thf('24', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         ((k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_B) @ X0)
% 0.41/0.57           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ sk_B @ X0)))),
% 0.41/0.57      inference('sup+', [status(thm)], ['22', '23'])).
% 0.41/0.57  thf('25', plain,
% 0.41/0.57      (((k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_B) @ sk_B)
% 0.41/0.57         = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.41/0.57      inference('sup+', [status(thm)], ['13', '24'])).
% 0.41/0.57  thf(idempotence_k3_xboole_0, axiom,
% 0.41/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.41/0.57  thf('26', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.41/0.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.41/0.57  thf(t100_xboole_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.57  thf('27', plain,
% 0.41/0.57      (![X2 : $i, X3 : $i]:
% 0.41/0.57         ((k4_xboole_0 @ X2 @ X3)
% 0.41/0.57           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.41/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.57  thf('28', plain,
% 0.41/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.57      inference('sup+', [status(thm)], ['26', '27'])).
% 0.41/0.57  thf(t4_boole, axiom,
% 0.41/0.57    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.41/0.57  thf('29', plain,
% 0.41/0.57      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.41/0.57      inference('cnf', [status(esa)], [t4_boole])).
% 0.41/0.57  thf('30', plain,
% 0.41/0.57      (((k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_B) @ sk_B)
% 0.41/0.57         = (k1_xboole_0))),
% 0.41/0.57      inference('demod', [status(thm)], ['25', '28', '29'])).
% 0.41/0.57  thf('31', plain,
% 0.41/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.41/0.57           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.41/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.41/0.57  thf('32', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.57           = (k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_B) @ 
% 0.41/0.57              (k5_xboole_0 @ sk_B @ X0)))),
% 0.41/0.57      inference('sup+', [status(thm)], ['30', '31'])).
% 0.41/0.57  thf('33', plain,
% 0.41/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.41/0.57           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.41/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.41/0.57  thf('34', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.41/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.41/0.57  thf('35', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i]:
% 0.41/0.57         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.41/0.57           = (k1_xboole_0))),
% 0.41/0.57      inference('sup+', [status(thm)], ['33', '34'])).
% 0.41/0.57  thf('36', plain,
% 0.41/0.57      (((k5_xboole_0 @ sk_B @ 
% 0.41/0.57         (k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_B)))
% 0.41/0.57         = (k1_xboole_0))),
% 0.41/0.57      inference('sup+', [status(thm)], ['32', '35'])).
% 0.41/0.57  thf('37', plain,
% 0.41/0.57      (![X2 : $i, X3 : $i]:
% 0.41/0.57         ((k4_xboole_0 @ X2 @ X3)
% 0.41/0.57           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.41/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.57  thf('38', plain,
% 0.41/0.57      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.41/0.57      inference('cnf', [status(esa)], [t4_boole])).
% 0.41/0.57  thf('39', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.41/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.57  thf('40', plain, (((sk_B) = (k1_xboole_0))),
% 0.41/0.57      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.41/0.57  thf(t69_enumset1, axiom,
% 0.41/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.57  thf('41', plain,
% 0.41/0.57      (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 0.41/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.57  thf('42', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.57      inference('demod', [status(thm)], ['12', '40', '41'])).
% 0.41/0.57  thf(t20_zfmisc_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.41/0.57         ( k1_tarski @ A ) ) <=>
% 0.41/0.57       ( ( A ) != ( B ) ) ))).
% 0.41/0.57  thf('43', plain,
% 0.41/0.57      (![X71 : $i, X72 : $i]:
% 0.41/0.57         (((X72) != (X71))
% 0.41/0.57          | ((k4_xboole_0 @ (k1_tarski @ X72) @ (k1_tarski @ X71))
% 0.41/0.57              != (k1_tarski @ X72)))),
% 0.41/0.57      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.41/0.57  thf('44', plain,
% 0.41/0.57      (![X71 : $i]:
% 0.41/0.57         ((k4_xboole_0 @ (k1_tarski @ X71) @ (k1_tarski @ X71))
% 0.41/0.57           != (k1_tarski @ X71))),
% 0.41/0.57      inference('simplify', [status(thm)], ['43'])).
% 0.41/0.57  thf('45', plain,
% 0.41/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.57      inference('sup+', [status(thm)], ['26', '27'])).
% 0.41/0.57  thf('46', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.41/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.41/0.57  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.57      inference('sup+', [status(thm)], ['45', '46'])).
% 0.41/0.57  thf('48', plain, (![X71 : $i]: ((k1_xboole_0) != (k1_tarski @ X71))),
% 0.41/0.57      inference('demod', [status(thm)], ['44', '47'])).
% 0.41/0.57  thf('49', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.41/0.57      inference('sup-', [status(thm)], ['42', '48'])).
% 0.41/0.57  thf('50', plain, ($false), inference('simplify', [status(thm)], ['49'])).
% 0.41/0.57  
% 0.41/0.57  % SZS output end Refutation
% 0.41/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
