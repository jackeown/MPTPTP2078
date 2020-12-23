%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bSKGQad5Z1

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 240 expanded)
%              Number of leaves         :   27 (  87 expanded)
%              Depth                    :   18
%              Number of atoms          :  492 (1468 expanded)
%              Number of equality atoms :   71 ( 193 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('4',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('8',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('9',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    r1_tarski @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('13',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_tarski @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','13'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('16',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('17',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','26'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('28',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('32',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','30','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('34',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('41',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('46',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','41','47'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('49',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('50',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','48','49'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('51',plain,(
    ! [X68: $i,X69: $i] :
      ( ( X69 != X68 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X69 ) @ ( k1_tarski @ X68 ) )
       != ( k1_tarski @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('52',plain,(
    ! [X68: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X68 ) @ ( k1_tarski @ X68 ) )
     != ( k1_tarski @ X68 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('54',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X68: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X68 ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bSKGQad5Z1
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:50:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 212 iterations in 0.071s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(t50_zfmisc_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t7_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.52  thf('2', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.20/0.52      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf(t3_xboole_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.52  thf('4', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('5', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf(l51_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X66 : $i, X67 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 0.20/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.52  thf('7', plain, (((k3_tarski @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.52  thf('8', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.20/0.52  thf('9', plain, (((k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.52  thf('11', plain, ((r1_tarski @ sk_A @ k1_xboole_0)),
% 0.20/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.52  thf('13', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain, (((k2_tarski @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '13'])).
% 0.20/0.52  thf(t92_xboole_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('15', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.52  thf('16', plain, (((k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('17', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('18', plain, (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf(t95_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k3_xboole_0 @ A @ B ) =
% 0.20/0.52       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         ((k3_xboole_0 @ X13 @ X14)
% 0.20/0.52           = (k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 0.20/0.52              (k2_xboole_0 @ X13 @ X14)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.20/0.52  thf(t91_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.52       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.20/0.52           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         ((k3_xboole_0 @ X13 @ X14)
% 0.20/0.52           = (k5_xboole_0 @ X13 @ 
% 0.20/0.52              (k5_xboole_0 @ X14 @ (k2_xboole_0 @ X13 @ X14))))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (((k3_xboole_0 @ k1_xboole_0 @ sk_B)
% 0.20/0.52         = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ sk_B @ k1_xboole_0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['18', '21'])).
% 0.20/0.52  thf(t5_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.52  thf('23', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k5_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.20/0.52           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_B) @ X0)
% 0.20/0.52           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ sk_B @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (((k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_B) @ sk_B)
% 0.20/0.52         = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['15', '26'])).
% 0.20/0.52  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.52  thf('28', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.52  thf(t100_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.52           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf(t4_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_B) @ sk_B)
% 0.20/0.52         = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['27', '30', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k5_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('34', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.20/0.52           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.52           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (((k5_xboole_0 @ k1_xboole_0 @ sk_B)
% 0.20/0.52         = (k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_B)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['33', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k5_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.52           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.52  thf('41', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         ((k3_xboole_0 @ X13 @ X14)
% 0.20/0.52           = (k5_xboole_0 @ X13 @ 
% 0.20/0.52              (k5_xboole_0 @ X14 @ (k2_xboole_0 @ X13 @ X14))))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.52           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 0.20/0.52           = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.52  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.52  thf('46', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.52  thf('47', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.52  thf('48', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['32', '41', '47'])).
% 0.20/0.52  thf(t69_enumset1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.52  thf('50', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '48', '49'])).
% 0.20/0.52  thf(t20_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.52         ( k1_tarski @ A ) ) <=>
% 0.20/0.52       ( ( A ) != ( B ) ) ))).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X68 : $i, X69 : $i]:
% 0.20/0.52         (((X69) != (X68))
% 0.20/0.52          | ((k4_xboole_0 @ (k1_tarski @ X69) @ (k1_tarski @ X68))
% 0.20/0.52              != (k1_tarski @ X69)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X68 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ (k1_tarski @ X68) @ (k1_tarski @ X68))
% 0.20/0.52           != (k1_tarski @ X68))),
% 0.20/0.52      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('54', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.52  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['53', '54'])).
% 0.20/0.52  thf('56', plain, (![X68 : $i]: ((k1_xboole_0) != (k1_tarski @ X68))),
% 0.20/0.52      inference('demod', [status(thm)], ['52', '55'])).
% 0.20/0.52  thf('57', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['50', '56'])).
% 0.20/0.52  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
