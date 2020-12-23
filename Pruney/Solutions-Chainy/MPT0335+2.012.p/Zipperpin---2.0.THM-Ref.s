%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PVB3dzO2fl

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 134 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  590 (1002 expanded)
%              Number of equality atoms :   70 ( 121 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X29 ) @ X28 )
        = X28 )
      | ~ ( r2_hidden @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ sk_A ),
    inference('sup+',[status(thm)],['2','3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X6 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('24',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,
    ( ( k1_tarski @ sk_D )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['17','25','30','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('53',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['36','55'])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A ) ),
    inference('sup+',[status(thm)],['35','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['32','60'])).

thf('62',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PVB3dzO2fl
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.73  % Solved by: fo/fo7.sh
% 0.21/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.73  % done 440 iterations in 0.278s
% 0.21/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.73  % SZS output start Refutation
% 0.21/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.73  thf(t148_zfmisc_1, conjecture,
% 0.21/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.73     ( ( ( r1_tarski @ A @ B ) & 
% 0.21/0.73         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.21/0.73         ( r2_hidden @ D @ A ) ) =>
% 0.21/0.73       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.21/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.73    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.73        ( ( ( r1_tarski @ A @ B ) & 
% 0.21/0.73            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.21/0.73            ( r2_hidden @ D @ A ) ) =>
% 0.21/0.73          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.21/0.73    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.21/0.73  thf('0', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.21/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.73  thf(l22_zfmisc_1, axiom,
% 0.21/0.73    (![A:$i,B:$i]:
% 0.21/0.73     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.73       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.73  thf('1', plain,
% 0.21/0.73      (![X28 : $i, X29 : $i]:
% 0.21/0.73         (((k2_xboole_0 @ (k1_tarski @ X29) @ X28) = (X28))
% 0.21/0.73          | ~ (r2_hidden @ X29 @ X28))),
% 0.21/0.73      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.21/0.73  thf('2', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (sk_A))),
% 0.21/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.73  thf(t7_xboole_1, axiom,
% 0.21/0.73    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.73  thf('3', plain,
% 0.21/0.73      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.21/0.73      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.73  thf('4', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ sk_A)),
% 0.21/0.73      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.73  thf(l32_xboole_1, axiom,
% 0.21/0.73    (![A:$i,B:$i]:
% 0.21/0.73     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.73  thf('5', plain,
% 0.21/0.73      (![X6 : $i, X8 : $i]:
% 0.21/0.73         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.21/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.73  thf('6', plain,
% 0.21/0.73      (((k4_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k1_xboole_0))),
% 0.21/0.73      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.73  thf(t47_xboole_1, axiom,
% 0.21/0.73    (![A:$i,B:$i]:
% 0.21/0.73     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.73  thf('7', plain,
% 0.21/0.73      (![X12 : $i, X13 : $i]:
% 0.21/0.73         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.21/0.73           = (k4_xboole_0 @ X12 @ X13))),
% 0.21/0.73      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.73  thf('8', plain,
% 0.21/0.73      (![X6 : $i, X7 : $i]:
% 0.21/0.73         ((r1_tarski @ X6 @ X7) | ((k4_xboole_0 @ X6 @ X7) != (k1_xboole_0)))),
% 0.21/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.73  thf('9', plain,
% 0.21/0.73      (![X0 : $i, X1 : $i]:
% 0.21/0.73         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.21/0.73          | (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.73  thf('10', plain,
% 0.21/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.73        | (r1_tarski @ (k1_tarski @ sk_D) @ 
% 0.21/0.73           (k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A)))),
% 0.21/0.73      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.73  thf('11', plain,
% 0.21/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.73  thf('12', plain,
% 0.21/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.73        | (r1_tarski @ (k1_tarski @ sk_D) @ 
% 0.21/0.73           (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D))))),
% 0.21/0.73      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.73  thf('13', plain,
% 0.21/0.73      ((r1_tarski @ (k1_tarski @ sk_D) @ 
% 0.21/0.73        (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))),
% 0.21/0.73      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.73  thf('14', plain,
% 0.21/0.73      (![X6 : $i, X8 : $i]:
% 0.21/0.73         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.21/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.73  thf('15', plain,
% 0.21/0.73      (((k4_xboole_0 @ (k1_tarski @ sk_D) @ 
% 0.21/0.73         (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D))) = (k1_xboole_0))),
% 0.21/0.73      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.73  thf(t48_xboole_1, axiom,
% 0.21/0.73    (![A:$i,B:$i]:
% 0.21/0.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.73  thf('16', plain,
% 0.21/0.73      (![X14 : $i, X15 : $i]:
% 0.21/0.73         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.73           = (k3_xboole_0 @ X14 @ X15))),
% 0.21/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.73  thf('17', plain,
% 0.21/0.73      (((k4_xboole_0 @ (k1_tarski @ sk_D) @ k1_xboole_0)
% 0.21/0.73         = (k3_xboole_0 @ (k1_tarski @ sk_D) @ 
% 0.21/0.73            (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D))))),
% 0.21/0.73      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.74  thf(d10_xboole_0, axiom,
% 0.21/0.74    (![A:$i,B:$i]:
% 0.21/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.74  thf('18', plain,
% 0.21/0.74      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.21/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.74  thf('19', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.21/0.74      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.74  thf('20', plain,
% 0.21/0.74      (![X6 : $i, X8 : $i]:
% 0.21/0.74         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.21/0.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.74  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.74      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.74  thf('22', plain,
% 0.21/0.74      (![X14 : $i, X15 : $i]:
% 0.21/0.74         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.74           = (k3_xboole_0 @ X14 @ X15))),
% 0.21/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.74  thf('23', plain,
% 0.21/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.74      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.74  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.74  thf('24', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.21/0.74      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.74  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.74      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.74  thf('26', plain,
% 0.21/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.74  thf('27', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.21/0.74      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.74  thf(t16_xboole_1, axiom,
% 0.21/0.74    (![A:$i,B:$i,C:$i]:
% 0.21/0.74     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.74       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.74  thf('28', plain,
% 0.21/0.74      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.74         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 0.21/0.74           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.21/0.74      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.21/0.74  thf('29', plain,
% 0.21/0.74      (![X0 : $i, X1 : $i]:
% 0.21/0.74         ((k3_xboole_0 @ X0 @ X1)
% 0.21/0.74           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.74      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.74  thf('30', plain,
% 0.21/0.74      (![X0 : $i, X1 : $i]:
% 0.21/0.74         ((k3_xboole_0 @ X0 @ X1)
% 0.21/0.74           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.74      inference('sup+', [status(thm)], ['26', '29'])).
% 0.21/0.74  thf('31', plain,
% 0.21/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.74  thf('32', plain,
% 0.21/0.74      (((k1_tarski @ sk_D) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))),
% 0.21/0.74      inference('demod', [status(thm)], ['17', '25', '30', '31'])).
% 0.21/0.74  thf('33', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.21/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.74  thf('34', plain,
% 0.21/0.74      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.74         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 0.21/0.74           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.21/0.74      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.21/0.74  thf('35', plain,
% 0.21/0.74      (![X0 : $i]:
% 0.21/0.74         ((k3_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.21/0.74           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.21/0.74      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.74  thf('36', plain,
% 0.21/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.74  thf('37', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.74  thf('38', plain,
% 0.21/0.74      (![X6 : $i, X8 : $i]:
% 0.21/0.74         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.21/0.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.74  thf('39', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.74      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.74  thf('40', plain,
% 0.21/0.74      (![X0 : $i, X1 : $i]:
% 0.21/0.74         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.21/0.74          | (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.74      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.74  thf('41', plain,
% 0.21/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.74        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.74      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.74  thf('42', plain,
% 0.21/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.74  thf('43', plain,
% 0.21/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.74        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.21/0.74      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.74  thf('44', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.74      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.74  thf('45', plain,
% 0.21/0.74      (![X6 : $i, X8 : $i]:
% 0.21/0.74         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.21/0.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.74  thf('46', plain,
% 0.21/0.74      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 0.21/0.74      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.74  thf('47', plain,
% 0.21/0.74      (![X14 : $i, X15 : $i]:
% 0.21/0.74         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.74           = (k3_xboole_0 @ X14 @ X15))),
% 0.21/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.74  thf('48', plain,
% 0.21/0.74      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.21/0.74         = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.21/0.74      inference('sup+', [status(thm)], ['46', '47'])).
% 0.21/0.74  thf('49', plain,
% 0.21/0.74      (![X0 : $i, X1 : $i]:
% 0.21/0.74         ((k3_xboole_0 @ X0 @ X1)
% 0.21/0.74           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.74      inference('sup+', [status(thm)], ['26', '29'])).
% 0.21/0.74  thf('50', plain,
% 0.21/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.74  thf('51', plain,
% 0.21/0.74      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.74      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.21/0.74  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.74      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.74  thf('53', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.74      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.74  thf('54', plain,
% 0.21/0.74      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.74         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 0.21/0.74           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.21/0.74      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.21/0.74  thf('55', plain,
% 0.21/0.74      (![X0 : $i]:
% 0.21/0.74         ((k3_xboole_0 @ sk_A @ X0)
% 0.21/0.74           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.21/0.74      inference('sup+', [status(thm)], ['53', '54'])).
% 0.21/0.74  thf('56', plain,
% 0.21/0.74      (![X0 : $i]:
% 0.21/0.74         ((k3_xboole_0 @ sk_A @ X0)
% 0.21/0.74           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 0.21/0.74      inference('sup+', [status(thm)], ['36', '55'])).
% 0.21/0.74  thf('57', plain,
% 0.21/0.74      (((k3_xboole_0 @ sk_A @ sk_C) = (k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A))),
% 0.21/0.74      inference('sup+', [status(thm)], ['35', '56'])).
% 0.21/0.74  thf('58', plain,
% 0.21/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.74  thf('59', plain,
% 0.21/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.74  thf('60', plain,
% 0.21/0.74      (((k3_xboole_0 @ sk_C @ sk_A) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))),
% 0.21/0.74      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.74  thf('61', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D))),
% 0.21/0.74      inference('sup+', [status(thm)], ['32', '60'])).
% 0.21/0.74  thf('62', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 0.21/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.74  thf('63', plain,
% 0.21/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.74  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 0.21/0.74      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.74  thf('65', plain, ($false),
% 0.21/0.74      inference('simplify_reflect-', [status(thm)], ['61', '64'])).
% 0.21/0.74  
% 0.21/0.74  % SZS output end Refutation
% 0.21/0.74  
% 0.21/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
