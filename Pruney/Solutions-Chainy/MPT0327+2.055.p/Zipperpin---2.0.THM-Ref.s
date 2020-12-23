%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aGK9bk8iEV

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:57 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 693 expanded)
%              Number of leaves         :   23 ( 220 expanded)
%              Depth                    :   19
%              Number of atoms          :  559 (4812 expanded)
%              Number of equality atoms :   64 ( 619 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X29: $i,X31: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X29 ) @ X31 )
      | ~ ( r2_hidden @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['4','30'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('32',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37 != X39 )
      | ~ ( r2_hidden @ X37 @ ( k4_xboole_0 @ X38 @ ( k1_tarski @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('33',plain,(
    ! [X38: $i,X39: $i] :
      ~ ( r2_hidden @ X39 @ ( k4_xboole_0 @ X38 @ ( k1_tarski @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','28'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','28'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','43'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('45',plain,(
    ! [X32: $i,X34: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X32 ) @ X34 )
        = ( k1_tarski @ X32 ) )
      | ( r2_hidden @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['4','30'])).

thf('50',plain,(
    ( k2_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('52',plain,(
    ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
     != sk_B )
    | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('56',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('57',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['44','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aGK9bk8iEV
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:36:00 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 354 iterations in 0.166s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(t140_zfmisc_1, conjecture,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( r2_hidden @ A @ B ) =>
% 0.45/0.64       ( ( k2_xboole_0 @
% 0.45/0.64           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.45/0.64         ( B ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i]:
% 0.45/0.64        ( ( r2_hidden @ A @ B ) =>
% 0.45/0.64          ( ( k2_xboole_0 @
% 0.45/0.64              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.45/0.64            ( B ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.45/0.64  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(l1_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (![X29 : $i, X31 : $i]:
% 0.45/0.64         ((r1_tarski @ (k1_tarski @ X29) @ X31) | ~ (r2_hidden @ X29 @ X31))),
% 0.45/0.64      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.45/0.64  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.45/0.64      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.64  thf(t12_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i]:
% 0.45/0.64         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.45/0.64      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.45/0.64  thf('4', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.64  thf(t98_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X17 : $i, X18 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ X17 @ X18)
% 0.45/0.64           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.64  thf(d10_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.64  thf('7', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.45/0.64      inference('simplify', [status(thm)], ['6'])).
% 0.45/0.64  thf(l32_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (![X4 : $i, X6 : $i]:
% 0.45/0.64         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.64  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.64  thf(t51_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.45/0.64       ( A ) ))).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (![X12 : $i, X13 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k4_xboole_0 @ X12 @ X13))
% 0.45/0.64           = (X12))),
% 0.45/0.64      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['9', '10'])).
% 0.45/0.64  thf(t1_boole, axiom,
% 0.45/0.64    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.64  thf('12', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.45/0.64      inference('cnf', [status(esa)], [t1_boole])).
% 0.45/0.64  thf('13', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf(t100_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X7 @ X8)
% 0.45/0.64           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['13', '14'])).
% 0.45/0.64  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.64  thf('17', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf(t91_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.64       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.45/0.64           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.64           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.64  thf('20', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.64           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['20', '21'])).
% 0.45/0.64  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      (![X17 : $i, X18 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ X17 @ X18)
% 0.45/0.64           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['23', '24'])).
% 0.45/0.64  thf(idempotence_k2_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.64  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.45/0.64  thf('27', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.64  thf('28', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['22', '27'])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['19', '28'])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.64           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['5', '29'])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.64         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['4', '30'])).
% 0.45/0.64  thf(t64_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.45/0.64       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.45/0.64         (((X37) != (X39))
% 0.45/0.64          | ~ (r2_hidden @ X37 @ (k4_xboole_0 @ X38 @ (k1_tarski @ X39))))),
% 0.45/0.64      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      (![X38 : $i, X39 : $i]:
% 0.45/0.64         ~ (r2_hidden @ X39 @ (k4_xboole_0 @ X38 @ (k1_tarski @ X39)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['32'])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (~ (r2_hidden @ sk_A @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['31', '33'])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.45/0.64           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.45/0.64  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf('37', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.45/0.64           = (k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['35', '36'])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['19', '28'])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.45/0.64           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['37', '38'])).
% 0.45/0.64  thf('40', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.64  thf('41', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.45/0.64      inference('demod', [status(thm)], ['39', '40'])).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['19', '28'])).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['41', '42'])).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      (~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['34', '43'])).
% 0.45/0.64  thf(l33_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.64       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.45/0.64  thf('45', plain,
% 0.45/0.64      (![X32 : $i, X34 : $i]:
% 0.45/0.64         (((k4_xboole_0 @ (k1_tarski @ X32) @ X34) = (k1_tarski @ X32))
% 0.45/0.64          | (r2_hidden @ X32 @ X34))),
% 0.45/0.64      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.45/0.64  thf('46', plain,
% 0.45/0.64      (![X17 : $i, X18 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ X17 @ X18)
% 0.45/0.64           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (((k2_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.45/0.64            = (k5_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.45/0.64          | (r2_hidden @ X0 @ X1))),
% 0.45/0.64      inference('sup+', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf('48', plain,
% 0.45/0.64      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.45/0.64         (k1_tarski @ sk_A)) != (sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('49', plain,
% 0.45/0.64      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.64         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['4', '30'])).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      (((k2_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.45/0.64         (k1_tarski @ sk_A)) != (sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['48', '49'])).
% 0.45/0.64  thf('51', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['41', '42'])).
% 0.45/0.64  thf('52', plain,
% 0.45/0.64      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.45/0.64         (k1_tarski @ sk_A)) != (sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('53', plain,
% 0.45/0.64      ((((k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.45/0.64          (k1_tarski @ sk_A)) != (sk_B))
% 0.45/0.64        | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['47', '52'])).
% 0.45/0.64  thf('54', plain,
% 0.45/0.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.45/0.64           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.45/0.64  thf('55', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf('56', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.64  thf('57', plain,
% 0.45/0.64      ((((sk_B) != (sk_B))
% 0.45/0.64        | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.45/0.64      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.45/0.64  thf('58', plain,
% 0.45/0.64      ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['57'])).
% 0.45/0.64  thf('59', plain, ($false), inference('demod', [status(thm)], ['44', '58'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
