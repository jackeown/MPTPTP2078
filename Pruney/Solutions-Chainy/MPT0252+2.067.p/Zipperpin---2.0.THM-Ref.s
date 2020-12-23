%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MQSnQwmPlW

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:25 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 119 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  490 ( 791 expanded)
%              Number of equality atoms :   37 (  53 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r2_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('6',plain,(
    ~ ( r2_xboole_0 @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( r2_hidden @ X70 @ X69 )
      | ~ ( r1_tarski @ ( k2_tarski @ X68 @ X70 ) @ X69 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('13',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( r2_hidden @ X68 @ X69 )
      | ~ ( r1_tarski @ ( k2_tarski @ X68 @ X70 ) @ X69 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X68: $i,X70: $i,X71: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X68 @ X70 ) @ X71 )
      | ~ ( r2_hidden @ X70 @ X71 )
      | ~ ( r2_hidden @ X68 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X0 @ X1 )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( r2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r2_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','22'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( r2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','27'])).

thf('29',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','28'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('41',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('42',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','45'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','46'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('49',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( r2_hidden @ X68 @ X69 )
      | ~ ( r1_tarski @ ( k2_tarski @ X68 @ X70 ) @ X69 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('51',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MQSnQwmPlW
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.83  % Solved by: fo/fo7.sh
% 0.59/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.83  % done 533 iterations in 0.368s
% 0.59/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.83  % SZS output start Refutation
% 0.59/0.83  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.59/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.83  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.59/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.83  thf(t47_zfmisc_1, conjecture,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.59/0.83       ( r2_hidden @ A @ C ) ))).
% 0.59/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.83    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.83        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.59/0.83          ( r2_hidden @ A @ C ) ) )),
% 0.59/0.83    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.59/0.83  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(t7_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.83  thf('1', plain,
% 0.59/0.83      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.59/0.83      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.59/0.83  thf(d8_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.59/0.83       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.59/0.83  thf('2', plain,
% 0.59/0.83      (![X2 : $i, X4 : $i]:
% 0.59/0.83         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.59/0.83      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.59/0.83  thf('3', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 0.59/0.83          | (r2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.83  thf('4', plain,
% 0.59/0.83      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(t60_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.59/0.83  thf('5', plain,
% 0.59/0.83      (![X9 : $i, X10 : $i]:
% 0.59/0.83         (~ (r1_tarski @ X9 @ X10) | ~ (r2_xboole_0 @ X10 @ X9))),
% 0.59/0.83      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.59/0.83  thf('6', plain,
% 0.59/0.83      (~ (r2_xboole_0 @ sk_C @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.59/0.83      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.83  thf(idempotence_k2_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.59/0.83  thf('7', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.59/0.83      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.59/0.83  thf('8', plain,
% 0.59/0.83      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.59/0.83      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.59/0.83  thf('9', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.59/0.83      inference('sup+', [status(thm)], ['7', '8'])).
% 0.59/0.83  thf(t38_zfmisc_1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.59/0.83       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.59/0.83  thf('10', plain,
% 0.59/0.83      (![X68 : $i, X69 : $i, X70 : $i]:
% 0.59/0.83         ((r2_hidden @ X70 @ X69)
% 0.59/0.83          | ~ (r1_tarski @ (k2_tarski @ X68 @ X70) @ X69))),
% 0.59/0.83      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.59/0.83  thf('11', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['9', '10'])).
% 0.59/0.83  thf('12', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.59/0.83      inference('sup+', [status(thm)], ['7', '8'])).
% 0.59/0.83  thf('13', plain,
% 0.59/0.83      (![X68 : $i, X69 : $i, X70 : $i]:
% 0.59/0.83         ((r2_hidden @ X68 @ X69)
% 0.59/0.83          | ~ (r1_tarski @ (k2_tarski @ X68 @ X70) @ X69))),
% 0.59/0.83      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.59/0.83  thf('14', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.83  thf('15', plain,
% 0.59/0.83      (![X68 : $i, X70 : $i, X71 : $i]:
% 0.59/0.83         ((r1_tarski @ (k2_tarski @ X68 @ X70) @ X71)
% 0.59/0.83          | ~ (r2_hidden @ X70 @ X71)
% 0.59/0.83          | ~ (r2_hidden @ X68 @ X71))),
% 0.59/0.83      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.59/0.83  thf('16', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.59/0.83          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.83  thf('17', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['11', '16'])).
% 0.59/0.83  thf('18', plain,
% 0.59/0.83      (![X2 : $i, X4 : $i]:
% 0.59/0.83         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.59/0.83      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.59/0.83  thf('19', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))
% 0.59/0.83          | (r2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['17', '18'])).
% 0.59/0.83  thf('20', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['11', '16'])).
% 0.59/0.83  thf('21', plain,
% 0.59/0.83      (![X9 : $i, X10 : $i]:
% 0.59/0.83         (~ (r1_tarski @ X9 @ X10) | ~ (r2_xboole_0 @ X10 @ X9))),
% 0.59/0.83      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.59/0.83  thf('22', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ~ (r2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))),
% 0.59/0.83      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.83  thf('23', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.59/0.83      inference('clc', [status(thm)], ['19', '22'])).
% 0.59/0.83  thf(l51_zfmisc_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.83  thf('24', plain,
% 0.59/0.83      (![X66 : $i, X67 : $i]:
% 0.59/0.83         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 0.59/0.83      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.59/0.83  thf('25', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['23', '24'])).
% 0.59/0.83  thf('26', plain,
% 0.59/0.83      (![X66 : $i, X67 : $i]:
% 0.59/0.83         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 0.59/0.83      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.59/0.83  thf('27', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['25', '26'])).
% 0.59/0.83  thf('28', plain,
% 0.59/0.83      (~ (r2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.59/0.83      inference('demod', [status(thm)], ['6', '27'])).
% 0.59/0.83  thf('29', plain,
% 0.59/0.83      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['3', '28'])).
% 0.59/0.83  thf(t95_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( k3_xboole_0 @ A @ B ) =
% 0.59/0.83       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.59/0.83  thf('30', plain,
% 0.59/0.83      (![X17 : $i, X18 : $i]:
% 0.59/0.83         ((k3_xboole_0 @ X17 @ X18)
% 0.59/0.83           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.59/0.83              (k2_xboole_0 @ X17 @ X18)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.59/0.83  thf(t91_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.83       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.59/0.83  thf('31', plain,
% 0.59/0.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.83         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.59/0.83           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.83  thf('32', plain,
% 0.59/0.83      (![X17 : $i, X18 : $i]:
% 0.59/0.83         ((k3_xboole_0 @ X17 @ X18)
% 0.59/0.83           = (k5_xboole_0 @ X17 @ 
% 0.59/0.83              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 0.59/0.83      inference('demod', [status(thm)], ['30', '31'])).
% 0.59/0.83  thf('33', plain,
% 0.59/0.83      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.59/0.83         = (k5_xboole_0 @ sk_C @ 
% 0.59/0.83            (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['29', '32'])).
% 0.59/0.83  thf(commutativity_k5_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.59/0.83  thf('34', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.59/0.83  thf(t92_xboole_1, axiom,
% 0.59/0.83    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.59/0.83  thf('35', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.59/0.83      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.59/0.83  thf('36', plain,
% 0.59/0.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.83         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.59/0.83           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.83  thf('37', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.59/0.83           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['35', '36'])).
% 0.59/0.83  thf('38', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.59/0.83      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.59/0.83  thf('39', plain,
% 0.59/0.83      (![X17 : $i, X18 : $i]:
% 0.59/0.83         ((k3_xboole_0 @ X17 @ X18)
% 0.59/0.83           = (k5_xboole_0 @ X17 @ 
% 0.59/0.83              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 0.59/0.83      inference('demod', [status(thm)], ['30', '31'])).
% 0.59/0.83  thf('40', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k3_xboole_0 @ X0 @ X0)
% 0.59/0.83           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['38', '39'])).
% 0.59/0.83  thf(idempotence_k3_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.59/0.83  thf('41', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.59/0.83      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.59/0.83  thf('42', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.59/0.83      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.59/0.83  thf('43', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.83      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.59/0.83  thf('44', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.59/0.83  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['43', '44'])).
% 0.59/0.83  thf('46', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('demod', [status(thm)], ['37', '45'])).
% 0.59/0.83  thf('47', plain,
% 0.59/0.83      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.59/0.83         = (k2_tarski @ sk_A @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)], ['33', '34', '46'])).
% 0.59/0.83  thf(t17_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.83  thf('48', plain,
% 0.59/0.83      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.59/0.83      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.59/0.83  thf('49', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.59/0.83      inference('sup+', [status(thm)], ['47', '48'])).
% 0.59/0.83  thf('50', plain,
% 0.59/0.83      (![X68 : $i, X69 : $i, X70 : $i]:
% 0.59/0.83         ((r2_hidden @ X68 @ X69)
% 0.59/0.83          | ~ (r1_tarski @ (k2_tarski @ X68 @ X70) @ X69))),
% 0.59/0.83      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.59/0.83  thf('51', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.59/0.83      inference('sup-', [status(thm)], ['49', '50'])).
% 0.59/0.83  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.59/0.83  
% 0.59/0.83  % SZS output end Refutation
% 0.59/0.83  
% 0.59/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
