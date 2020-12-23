%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FeTBESawH5

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:25 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 122 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  495 ( 810 expanded)
%              Number of equality atoms :   38 (  56 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r2_xboole_0 @ X13 @ X12 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
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
    ! [X69: $i,X70: $i,X71: $i] :
      ( ( r2_hidden @ X71 @ X70 )
      | ~ ( r1_tarski @ ( k2_tarski @ X69 @ X71 ) @ X70 ) ) ),
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
    ! [X69: $i,X70: $i,X71: $i] :
      ( ( r2_hidden @ X69 @ X70 )
      | ~ ( r1_tarski @ ( k2_tarski @ X69 @ X71 ) @ X70 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X69: $i,X71: $i,X72: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X69 @ X71 ) @ X72 )
      | ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r2_hidden @ X69 @ X72 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r2_xboole_0 @ X13 @ X12 ) ) ),
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
    ! [X67: $i,X68: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X67 @ X68 ) )
      = ( k2_xboole_0 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X67: $i,X68: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X67 @ X68 ) )
      = ( k2_xboole_0 @ X67 @ X68 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ) ),
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

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

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
    ! [X69: $i,X70: $i,X71: $i] :
      ( ( r2_hidden @ X69 @ X70 )
      | ~ ( r1_tarski @ ( k2_tarski @ X69 @ X71 ) @ X70 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('51',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FeTBESawH5
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:36:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.09/1.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.09/1.28  % Solved by: fo/fo7.sh
% 1.09/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.09/1.28  % done 1141 iterations in 0.822s
% 1.09/1.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.09/1.28  % SZS output start Refutation
% 1.09/1.28  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 1.09/1.28  thf(sk_C_type, type, sk_C: $i).
% 1.09/1.28  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.09/1.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.09/1.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.09/1.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.09/1.28  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.09/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.09/1.28  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.09/1.28  thf(sk_B_type, type, sk_B: $i).
% 1.09/1.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.09/1.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.09/1.28  thf(t47_zfmisc_1, conjecture,
% 1.09/1.28    (![A:$i,B:$i,C:$i]:
% 1.09/1.28     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 1.09/1.28       ( r2_hidden @ A @ C ) ))).
% 1.09/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.09/1.28    (~( ![A:$i,B:$i,C:$i]:
% 1.09/1.28        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 1.09/1.28          ( r2_hidden @ A @ C ) ) )),
% 1.09/1.28    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 1.09/1.28  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 1.09/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.28  thf(t7_xboole_1, axiom,
% 1.09/1.28    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.09/1.28  thf('1', plain,
% 1.09/1.28      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 1.09/1.28      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.09/1.28  thf(d8_xboole_0, axiom,
% 1.09/1.28    (![A:$i,B:$i]:
% 1.09/1.28     ( ( r2_xboole_0 @ A @ B ) <=>
% 1.09/1.28       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 1.09/1.28  thf('2', plain,
% 1.09/1.28      (![X2 : $i, X4 : $i]:
% 1.09/1.28         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 1.09/1.28      inference('cnf', [status(esa)], [d8_xboole_0])).
% 1.09/1.28  thf('3', plain,
% 1.09/1.28      (![X0 : $i, X1 : $i]:
% 1.09/1.28         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 1.09/1.28          | (r2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.09/1.28      inference('sup-', [status(thm)], ['1', '2'])).
% 1.09/1.28  thf('4', plain,
% 1.09/1.28      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)),
% 1.09/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.28  thf(t60_xboole_1, axiom,
% 1.09/1.28    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 1.09/1.28  thf('5', plain,
% 1.09/1.28      (![X12 : $i, X13 : $i]:
% 1.09/1.28         (~ (r1_tarski @ X12 @ X13) | ~ (r2_xboole_0 @ X13 @ X12))),
% 1.09/1.28      inference('cnf', [status(esa)], [t60_xboole_1])).
% 1.09/1.28  thf('6', plain,
% 1.09/1.28      (~ (r2_xboole_0 @ sk_C @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 1.09/1.28      inference('sup-', [status(thm)], ['4', '5'])).
% 1.09/1.28  thf(idempotence_k2_xboole_0, axiom,
% 1.09/1.28    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.09/1.28  thf('7', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 1.09/1.28      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.09/1.28  thf('8', plain,
% 1.09/1.28      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 1.09/1.28      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.09/1.28  thf('9', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.09/1.28      inference('sup+', [status(thm)], ['7', '8'])).
% 1.09/1.28  thf(t38_zfmisc_1, axiom,
% 1.09/1.28    (![A:$i,B:$i,C:$i]:
% 1.09/1.28     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.09/1.28       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.09/1.28  thf('10', plain,
% 1.09/1.28      (![X69 : $i, X70 : $i, X71 : $i]:
% 1.09/1.28         ((r2_hidden @ X71 @ X70)
% 1.09/1.28          | ~ (r1_tarski @ (k2_tarski @ X69 @ X71) @ X70))),
% 1.09/1.28      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.09/1.28  thf('11', plain,
% 1.09/1.28      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 1.09/1.28      inference('sup-', [status(thm)], ['9', '10'])).
% 1.09/1.28  thf('12', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.09/1.28      inference('sup+', [status(thm)], ['7', '8'])).
% 1.09/1.28  thf('13', plain,
% 1.09/1.28      (![X69 : $i, X70 : $i, X71 : $i]:
% 1.09/1.28         ((r2_hidden @ X69 @ X70)
% 1.09/1.28          | ~ (r1_tarski @ (k2_tarski @ X69 @ X71) @ X70))),
% 1.09/1.28      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.09/1.28  thf('14', plain,
% 1.09/1.28      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 1.09/1.28      inference('sup-', [status(thm)], ['12', '13'])).
% 1.09/1.28  thf('15', plain,
% 1.09/1.28      (![X69 : $i, X71 : $i, X72 : $i]:
% 1.09/1.28         ((r1_tarski @ (k2_tarski @ X69 @ X71) @ X72)
% 1.09/1.28          | ~ (r2_hidden @ X71 @ X72)
% 1.09/1.28          | ~ (r2_hidden @ X69 @ X72))),
% 1.09/1.28      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.09/1.28  thf('16', plain,
% 1.09/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.28         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.09/1.28          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 1.09/1.28      inference('sup-', [status(thm)], ['14', '15'])).
% 1.09/1.28  thf('17', plain,
% 1.09/1.28      (![X0 : $i, X1 : $i]:
% 1.09/1.28         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 1.09/1.28      inference('sup-', [status(thm)], ['11', '16'])).
% 1.09/1.28  thf('18', plain,
% 1.09/1.28      (![X2 : $i, X4 : $i]:
% 1.09/1.28         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 1.09/1.28      inference('cnf', [status(esa)], [d8_xboole_0])).
% 1.09/1.28  thf('19', plain,
% 1.09/1.28      (![X0 : $i, X1 : $i]:
% 1.09/1.28         (((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))
% 1.09/1.28          | (r2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 1.09/1.28      inference('sup-', [status(thm)], ['17', '18'])).
% 1.09/1.28  thf('20', plain,
% 1.09/1.28      (![X0 : $i, X1 : $i]:
% 1.09/1.28         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 1.09/1.28      inference('sup-', [status(thm)], ['11', '16'])).
% 1.09/1.28  thf('21', plain,
% 1.09/1.28      (![X12 : $i, X13 : $i]:
% 1.09/1.28         (~ (r1_tarski @ X12 @ X13) | ~ (r2_xboole_0 @ X13 @ X12))),
% 1.09/1.28      inference('cnf', [status(esa)], [t60_xboole_1])).
% 1.09/1.28  thf('22', plain,
% 1.09/1.28      (![X0 : $i, X1 : $i]:
% 1.09/1.28         ~ (r2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))),
% 1.09/1.28      inference('sup-', [status(thm)], ['20', '21'])).
% 1.09/1.28  thf('23', plain,
% 1.09/1.28      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 1.09/1.28      inference('clc', [status(thm)], ['19', '22'])).
% 1.09/1.28  thf(l51_zfmisc_1, axiom,
% 1.09/1.28    (![A:$i,B:$i]:
% 1.09/1.28     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.09/1.28  thf('24', plain,
% 1.09/1.28      (![X67 : $i, X68 : $i]:
% 1.09/1.28         ((k3_tarski @ (k2_tarski @ X67 @ X68)) = (k2_xboole_0 @ X67 @ X68))),
% 1.09/1.28      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.09/1.28  thf('25', plain,
% 1.09/1.28      (![X0 : $i, X1 : $i]:
% 1.09/1.28         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.09/1.28      inference('sup+', [status(thm)], ['23', '24'])).
% 1.09/1.28  thf('26', plain,
% 1.09/1.28      (![X67 : $i, X68 : $i]:
% 1.09/1.28         ((k3_tarski @ (k2_tarski @ X67 @ X68)) = (k2_xboole_0 @ X67 @ X68))),
% 1.09/1.28      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.09/1.28  thf('27', plain,
% 1.09/1.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.09/1.28      inference('sup+', [status(thm)], ['25', '26'])).
% 1.09/1.28  thf('28', plain,
% 1.09/1.28      (~ (r2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 1.09/1.28      inference('demod', [status(thm)], ['6', '27'])).
% 1.09/1.28  thf('29', plain,
% 1.09/1.28      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 1.09/1.28      inference('sup-', [status(thm)], ['3', '28'])).
% 1.09/1.28  thf(t95_xboole_1, axiom,
% 1.09/1.28    (![A:$i,B:$i]:
% 1.09/1.28     ( ( k3_xboole_0 @ A @ B ) =
% 1.09/1.28       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.09/1.28  thf('30', plain,
% 1.09/1.28      (![X19 : $i, X20 : $i]:
% 1.09/1.28         ((k3_xboole_0 @ X19 @ X20)
% 1.09/1.28           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 1.09/1.28              (k2_xboole_0 @ X19 @ X20)))),
% 1.09/1.28      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.09/1.28  thf(t91_xboole_1, axiom,
% 1.09/1.28    (![A:$i,B:$i,C:$i]:
% 1.09/1.28     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.09/1.28       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.09/1.28  thf('31', plain,
% 1.09/1.28      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.09/1.28         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 1.09/1.28           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 1.09/1.28      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.09/1.28  thf('32', plain,
% 1.09/1.28      (![X19 : $i, X20 : $i]:
% 1.09/1.28         ((k3_xboole_0 @ X19 @ X20)
% 1.09/1.28           = (k5_xboole_0 @ X19 @ 
% 1.09/1.28              (k5_xboole_0 @ X20 @ (k2_xboole_0 @ X19 @ X20))))),
% 1.09/1.28      inference('demod', [status(thm)], ['30', '31'])).
% 1.09/1.28  thf('33', plain,
% 1.09/1.28      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.09/1.28         = (k5_xboole_0 @ sk_C @ 
% 1.09/1.28            (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 1.09/1.28      inference('sup+', [status(thm)], ['29', '32'])).
% 1.09/1.28  thf(commutativity_k5_xboole_0, axiom,
% 1.09/1.28    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.09/1.28  thf('34', plain,
% 1.09/1.28      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.09/1.29      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.09/1.29  thf('35', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.09/1.29      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.09/1.29  thf(t5_boole, axiom,
% 1.09/1.29    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.09/1.29  thf('36', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 1.09/1.29      inference('cnf', [status(esa)], [t5_boole])).
% 1.09/1.29  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.09/1.29      inference('sup+', [status(thm)], ['35', '36'])).
% 1.09/1.29  thf('38', plain,
% 1.09/1.29      (![X19 : $i, X20 : $i]:
% 1.09/1.29         ((k3_xboole_0 @ X19 @ X20)
% 1.09/1.29           = (k5_xboole_0 @ X19 @ 
% 1.09/1.29              (k5_xboole_0 @ X20 @ (k2_xboole_0 @ X19 @ X20))))),
% 1.09/1.29      inference('demod', [status(thm)], ['30', '31'])).
% 1.09/1.29  thf('39', plain,
% 1.09/1.29      (![X0 : $i]:
% 1.09/1.29         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 1.09/1.29           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.09/1.29      inference('sup+', [status(thm)], ['37', '38'])).
% 1.09/1.29  thf(t2_boole, axiom,
% 1.09/1.29    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.09/1.29  thf('40', plain,
% 1.09/1.29      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.09/1.29      inference('cnf', [status(esa)], [t2_boole])).
% 1.09/1.29  thf(t1_boole, axiom,
% 1.09/1.29    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.09/1.29  thf('41', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.09/1.29      inference('cnf', [status(esa)], [t1_boole])).
% 1.09/1.29  thf('42', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.09/1.29      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.09/1.29  thf('43', plain,
% 1.09/1.29      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.09/1.29         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 1.09/1.29           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 1.09/1.29      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.09/1.29  thf('44', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]:
% 1.09/1.29         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.09/1.29           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.09/1.29      inference('sup+', [status(thm)], ['42', '43'])).
% 1.09/1.29  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.09/1.29      inference('sup+', [status(thm)], ['35', '36'])).
% 1.09/1.29  thf('46', plain,
% 1.09/1.29      (![X0 : $i, X1 : $i]:
% 1.09/1.29         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.09/1.29      inference('demod', [status(thm)], ['44', '45'])).
% 1.09/1.29  thf('47', plain,
% 1.09/1.29      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.09/1.29         = (k2_tarski @ sk_A @ sk_B))),
% 1.09/1.29      inference('demod', [status(thm)], ['33', '34', '46'])).
% 1.09/1.29  thf(t17_xboole_1, axiom,
% 1.09/1.29    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.09/1.29  thf('48', plain,
% 1.09/1.29      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.09/1.29      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.09/1.29  thf('49', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 1.09/1.29      inference('sup+', [status(thm)], ['47', '48'])).
% 1.09/1.29  thf('50', plain,
% 1.09/1.29      (![X69 : $i, X70 : $i, X71 : $i]:
% 1.09/1.29         ((r2_hidden @ X69 @ X70)
% 1.09/1.29          | ~ (r1_tarski @ (k2_tarski @ X69 @ X71) @ X70))),
% 1.09/1.29      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.09/1.29  thf('51', plain, ((r2_hidden @ sk_A @ sk_C)),
% 1.09/1.29      inference('sup-', [status(thm)], ['49', '50'])).
% 1.09/1.29  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 1.09/1.29  
% 1.09/1.29  % SZS output end Refutation
% 1.09/1.29  
% 1.09/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
