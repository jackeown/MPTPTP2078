%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mVhzr2lgOs

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:08 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 193 expanded)
%              Number of leaves         :   23 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  512 (1482 expanded)
%              Number of equality atoms :   75 ( 203 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('13',plain,(
    ! [X47: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['9','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','16'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','22'])).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','16'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','16'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['9','14','15'])).

thf('34',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['23','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ ( k2_xboole_0 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('40',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X43
        = ( k2_tarski @ X41 @ X42 ) )
      | ( X43
        = ( k1_tarski @ X42 ) )
      | ( X43
        = ( k1_tarski @ X41 ) )
      | ( X43 = k1_xboole_0 )
      | ~ ( r1_tarski @ X43 @ ( k2_tarski @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mVhzr2lgOs
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:47:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.43/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.64  % Solved by: fo/fo7.sh
% 0.43/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.64  % done 419 iterations in 0.190s
% 0.43/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.64  % SZS output start Refutation
% 0.43/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.64  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.43/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.43/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.64  thf(t66_zfmisc_1, conjecture,
% 0.43/0.64    (![A:$i,B:$i]:
% 0.43/0.64     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.43/0.64          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.43/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.64    (~( ![A:$i,B:$i]:
% 0.43/0.64        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.43/0.64             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.43/0.64    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.43/0.64  thf('0', plain,
% 0.43/0.64      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.43/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.64  thf(t95_xboole_1, axiom,
% 0.43/0.64    (![A:$i,B:$i]:
% 0.43/0.64     ( ( k3_xboole_0 @ A @ B ) =
% 0.43/0.64       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.43/0.64  thf('1', plain,
% 0.43/0.64      (![X11 : $i, X12 : $i]:
% 0.43/0.64         ((k3_xboole_0 @ X11 @ X12)
% 0.43/0.64           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 0.43/0.64              (k2_xboole_0 @ X11 @ X12)))),
% 0.43/0.64      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.43/0.64  thf(t91_xboole_1, axiom,
% 0.43/0.64    (![A:$i,B:$i,C:$i]:
% 0.43/0.64     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.43/0.64       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.43/0.64  thf('2', plain,
% 0.43/0.64      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.43/0.64           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.43/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.43/0.64  thf('3', plain,
% 0.43/0.64      (![X11 : $i, X12 : $i]:
% 0.43/0.64         ((k3_xboole_0 @ X11 @ X12)
% 0.43/0.64           = (k5_xboole_0 @ X11 @ 
% 0.43/0.64              (k5_xboole_0 @ X12 @ (k2_xboole_0 @ X11 @ X12))))),
% 0.43/0.64      inference('demod', [status(thm)], ['1', '2'])).
% 0.43/0.64  thf(t92_xboole_1, axiom,
% 0.43/0.64    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.43/0.64  thf('4', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.43/0.64      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.43/0.64  thf('5', plain,
% 0.43/0.64      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.43/0.64           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.43/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.43/0.64  thf('6', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.43/0.64           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.64      inference('sup+', [status(thm)], ['4', '5'])).
% 0.43/0.64  thf('7', plain,
% 0.43/0.64      (![X11 : $i, X12 : $i]:
% 0.43/0.64         ((k3_xboole_0 @ X11 @ X12)
% 0.43/0.64           = (k5_xboole_0 @ X11 @ 
% 0.43/0.64              (k5_xboole_0 @ X12 @ (k2_xboole_0 @ X11 @ X12))))),
% 0.43/0.64      inference('demod', [status(thm)], ['1', '2'])).
% 0.43/0.64  thf('8', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.43/0.64           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.64      inference('sup+', [status(thm)], ['4', '5'])).
% 0.43/0.64  thf('9', plain,
% 0.43/0.64      (![X0 : $i]:
% 0.43/0.64         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 0.43/0.64           = (k3_xboole_0 @ X0 @ X0))),
% 0.43/0.64      inference('sup+', [status(thm)], ['7', '8'])).
% 0.43/0.64  thf(t69_enumset1, axiom,
% 0.43/0.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.43/0.64  thf('10', plain,
% 0.43/0.64      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.43/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.64  thf(l51_zfmisc_1, axiom,
% 0.43/0.64    (![A:$i,B:$i]:
% 0.43/0.64     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.64  thf('11', plain,
% 0.43/0.64      (![X45 : $i, X46 : $i]:
% 0.43/0.64         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.43/0.64      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.43/0.64  thf('12', plain,
% 0.43/0.64      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.43/0.64      inference('sup+', [status(thm)], ['10', '11'])).
% 0.43/0.64  thf(t31_zfmisc_1, axiom,
% 0.43/0.64    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.43/0.64  thf('13', plain, (![X47 : $i]: ((k3_tarski @ (k1_tarski @ X47)) = (X47))),
% 0.43/0.64      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.43/0.64  thf('14', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.43/0.64      inference('demod', [status(thm)], ['12', '13'])).
% 0.43/0.64  thf(idempotence_k3_xboole_0, axiom,
% 0.43/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.43/0.64  thf('15', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.43/0.64      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.43/0.64  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.64      inference('demod', [status(thm)], ['9', '14', '15'])).
% 0.43/0.64  thf('17', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.64      inference('demod', [status(thm)], ['6', '16'])).
% 0.43/0.64  thf('18', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.43/0.64           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.43/0.64      inference('sup+', [status(thm)], ['3', '17'])).
% 0.43/0.64  thf(t100_xboole_1, axiom,
% 0.43/0.64    (![A:$i,B:$i]:
% 0.43/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.43/0.64  thf('19', plain,
% 0.43/0.64      (![X1 : $i, X2 : $i]:
% 0.43/0.64         ((k4_xboole_0 @ X1 @ X2)
% 0.43/0.64           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.43/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.64  thf('20', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.43/0.64           = (k4_xboole_0 @ X1 @ X0))),
% 0.43/0.64      inference('demod', [status(thm)], ['18', '19'])).
% 0.43/0.64  thf('21', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.64      inference('demod', [status(thm)], ['6', '16'])).
% 0.43/0.64  thf('22', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         ((k2_xboole_0 @ X1 @ X0)
% 0.43/0.64           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.43/0.64      inference('sup+', [status(thm)], ['20', '21'])).
% 0.43/0.64  thf('23', plain,
% 0.43/0.64      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.43/0.64         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.43/0.64      inference('sup+', [status(thm)], ['0', '22'])).
% 0.43/0.64  thf('24', plain,
% 0.43/0.64      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.43/0.64           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.43/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.43/0.64  thf('25', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.43/0.64      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.43/0.64  thf('26', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.43/0.64           = (k1_xboole_0))),
% 0.43/0.64      inference('sup+', [status(thm)], ['24', '25'])).
% 0.43/0.64  thf('27', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.64      inference('demod', [status(thm)], ['6', '16'])).
% 0.43/0.64  thf('28', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.43/0.64           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.43/0.64      inference('sup+', [status(thm)], ['26', '27'])).
% 0.43/0.64  thf(t5_boole, axiom,
% 0.43/0.64    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.64  thf('29', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.43/0.64      inference('cnf', [status(esa)], [t5_boole])).
% 0.43/0.64  thf('30', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.43/0.64      inference('demod', [status(thm)], ['28', '29'])).
% 0.43/0.64  thf('31', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.43/0.64      inference('demod', [status(thm)], ['6', '16'])).
% 0.43/0.64  thf('32', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.43/0.64      inference('sup+', [status(thm)], ['30', '31'])).
% 0.43/0.64  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.64      inference('demod', [status(thm)], ['9', '14', '15'])).
% 0.43/0.64  thf('34', plain,
% 0.43/0.64      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.43/0.64      inference('demod', [status(thm)], ['23', '32', '33'])).
% 0.43/0.64  thf('35', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.43/0.64      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.43/0.64  thf(t29_xboole_1, axiom,
% 0.43/0.64    (![A:$i,B:$i,C:$i]:
% 0.43/0.64     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 0.43/0.64  thf('36', plain,
% 0.43/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.64         (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ (k2_xboole_0 @ X3 @ X5))),
% 0.43/0.64      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.43/0.64  thf('37', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.64      inference('sup+', [status(thm)], ['35', '36'])).
% 0.43/0.64  thf('38', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.43/0.64      inference('sup+', [status(thm)], ['34', '37'])).
% 0.43/0.64  thf('39', plain,
% 0.43/0.64      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.43/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.64  thf(l45_zfmisc_1, axiom,
% 0.43/0.64    (![A:$i,B:$i,C:$i]:
% 0.43/0.64     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.43/0.64       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.43/0.64            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.43/0.64  thf('40', plain,
% 0.43/0.64      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.43/0.64         (((X43) = (k2_tarski @ X41 @ X42))
% 0.43/0.64          | ((X43) = (k1_tarski @ X42))
% 0.43/0.64          | ((X43) = (k1_tarski @ X41))
% 0.43/0.64          | ((X43) = (k1_xboole_0))
% 0.43/0.64          | ~ (r1_tarski @ X43 @ (k2_tarski @ X41 @ X42)))),
% 0.43/0.64      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.43/0.64  thf('41', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.43/0.64          | ((X1) = (k1_xboole_0))
% 0.43/0.64          | ((X1) = (k1_tarski @ X0))
% 0.43/0.64          | ((X1) = (k1_tarski @ X0))
% 0.43/0.64          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.43/0.64      inference('sup-', [status(thm)], ['39', '40'])).
% 0.43/0.64  thf('42', plain,
% 0.43/0.64      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.43/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.64  thf('43', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.43/0.64          | ((X1) = (k1_xboole_0))
% 0.43/0.64          | ((X1) = (k1_tarski @ X0))
% 0.43/0.64          | ((X1) = (k1_tarski @ X0))
% 0.43/0.64          | ((X1) = (k1_tarski @ X0)))),
% 0.43/0.64      inference('demod', [status(thm)], ['41', '42'])).
% 0.43/0.64  thf('44', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         (((X1) = (k1_tarski @ X0))
% 0.43/0.64          | ((X1) = (k1_xboole_0))
% 0.43/0.64          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.43/0.64      inference('simplify', [status(thm)], ['43'])).
% 0.43/0.64  thf('45', plain,
% 0.43/0.64      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.43/0.64      inference('sup-', [status(thm)], ['38', '44'])).
% 0.43/0.64  thf('46', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.43/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.64  thf('47', plain, (((sk_A) != (k1_xboole_0))),
% 0.43/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.64  thf('48', plain, ($false),
% 0.43/0.64      inference('simplify_reflect-', [status(thm)], ['45', '46', '47'])).
% 0.43/0.64  
% 0.43/0.64  % SZS output end Refutation
% 0.43/0.64  
% 0.43/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
