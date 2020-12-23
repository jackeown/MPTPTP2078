%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MkJMTbLpCY

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 192 expanded)
%              Number of leaves         :   28 (  69 expanded)
%              Depth                    :   20
%              Number of atoms          :  507 (1471 expanded)
%              Number of equality atoms :   71 ( 266 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('5',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X51
        = ( k1_tarski @ X50 ) )
      | ( X51 = k1_xboole_0 )
      | ~ ( r1_tarski @ X51 @ ( k1_tarski @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('6',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['1','8'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['1','8'])).

thf('17',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('18',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X53 @ X54 ) )
      = ( k2_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('22',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,
    ( sk_B
    = ( k1_tarski @ ( k3_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','24'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('26',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X48 ) @ X49 )
      | ( r2_hidden @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r2_hidden @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('28',plain,(
    ! [X45: $i,X47: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X45 ) @ X47 )
      | ~ ( r2_hidden @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_B
    = ( k1_tarski @ ( k3_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B = sk_C )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['16','33'])).

thf('35',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','38'])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('45',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('46',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['41','49','50'])).

thf('52',plain,
    ( sk_C
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('54',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('55',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MkJMTbLpCY
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 158 iterations in 0.048s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(t92_xboole_1, axiom,
% 0.19/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.50  thf('0', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.50  thf(t44_zfmisc_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.19/0.50          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.50          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.50        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.19/0.50             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.50             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.19/0.50  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t7_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.19/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.50  thf('4', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.19/0.50      inference('sup+', [status(thm)], ['2', '3'])).
% 0.19/0.50  thf(l3_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.19/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X50 : $i, X51 : $i]:
% 0.19/0.50         (((X51) = (k1_tarski @ X50))
% 0.19/0.50          | ((X51) = (k1_xboole_0))
% 0.19/0.50          | ~ (r1_tarski @ X51 @ (k1_tarski @ X50)))),
% 0.19/0.50      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.50  thf('6', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.50  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('8', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf('9', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['1', '8'])).
% 0.19/0.50  thf(t95_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k3_xboole_0 @ A @ B ) =
% 0.19/0.50       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X15 : $i, X16 : $i]:
% 0.19/0.50         ((k3_xboole_0 @ X15 @ X16)
% 0.19/0.50           = (k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ 
% 0.19/0.50              (k2_xboole_0 @ X15 @ X16)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.19/0.50  thf(t91_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.50       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.50         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.19/0.50           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X15 : $i, X16 : $i]:
% 0.19/0.50         ((k3_xboole_0 @ X15 @ X16)
% 0.19/0.50           = (k5_xboole_0 @ X15 @ 
% 0.19/0.50              (k5_xboole_0 @ X16 @ (k2_xboole_0 @ X15 @ X16))))),
% 0.19/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.19/0.50         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_B)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['9', '12'])).
% 0.19/0.50  thf(commutativity_k5_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.19/0.50         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('16', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['1', '8'])).
% 0.19/0.50  thf('17', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf('18', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf(t69_enumset1, axiom,
% 0.19/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.50  thf(l51_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X53 : $i, X54 : $i]:
% 0.19/0.50         ((k3_tarski @ (k2_tarski @ X53 @ X54)) = (k2_xboole_0 @ X53 @ X54))),
% 0.19/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.50  thf(idempotence_k2_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.50  thf('22', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.19/0.50  thf('23', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.50  thf('24', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 0.19/0.50      inference('sup+', [status(thm)], ['18', '23'])).
% 0.19/0.50  thf('25', plain, (((sk_B) = (k1_tarski @ (k3_tarski @ sk_B)))),
% 0.19/0.50      inference('demod', [status(thm)], ['17', '24'])).
% 0.19/0.50  thf(l27_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X48 : $i, X49 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ (k1_tarski @ X48) @ X49) | (r2_hidden @ X48 @ X49))),
% 0.19/0.50      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ sk_B @ X0) | (r2_hidden @ (k3_tarski @ sk_B) @ X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf(l1_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X45 : $i, X47 : $i]:
% 0.19/0.50         ((r1_tarski @ (k1_tarski @ X45) @ X47) | ~ (r2_hidden @ X45 @ X47))),
% 0.19/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ sk_B @ X0)
% 0.19/0.50          | (r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B)) @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.50  thf('30', plain, (((sk_B) = (k1_tarski @ (k3_tarski @ sk_B)))),
% 0.19/0.50      inference('demod', [status(thm)], ['17', '24'])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | (r1_tarski @ sk_B @ X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf(t12_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (![X7 : $i, X8 : $i]:
% 0.19/0.50         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.19/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ sk_B @ X0) | ((k2_xboole_0 @ sk_B @ X0) = (X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf('34', plain, ((((sk_B) = (sk_C)) | (r1_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.50      inference('sup+', [status(thm)], ['16', '33'])).
% 0.19/0.50  thf('35', plain, (((sk_B) != (sk_C))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('36', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.19/0.50  thf(d7_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.19/0.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      (![X2 : $i, X3 : $i]:
% 0.19/0.50         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.50  thf('38', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      (((k1_xboole_0) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.19/0.50      inference('demod', [status(thm)], ['15', '38'])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.50         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.19/0.50           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.19/0.50           = (k5_xboole_0 @ sk_B @ 
% 0.19/0.50              (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['39', '40'])).
% 0.19/0.50  thf('42', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      (![X15 : $i, X16 : $i]:
% 0.19/0.50         ((k3_xboole_0 @ X15 @ X16)
% 0.19/0.50           = (k5_xboole_0 @ X15 @ 
% 0.19/0.50              (k5_xboole_0 @ X16 @ (k2_xboole_0 @ X15 @ X16))))),
% 0.19/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((k3_xboole_0 @ X0 @ X0)
% 0.19/0.50           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['42', '43'])).
% 0.19/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.50  thf('45', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.19/0.50  thf('46', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.50  thf('47', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.50      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.50  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['47', '48'])).
% 0.19/0.50  thf('50', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.50         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.19/0.50           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((X0)
% 0.19/0.50           = (k5_xboole_0 @ sk_B @ 
% 0.19/0.50              (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ X0))))),
% 0.19/0.50      inference('demod', [status(thm)], ['41', '49', '50'])).
% 0.19/0.50  thf('52', plain,
% 0.19/0.50      (((sk_C) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['0', '51'])).
% 0.19/0.50  thf('53', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.50      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.19/0.50  thf('54', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.50  thf('55', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.50      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.19/0.50  thf('56', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('57', plain, ($false),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
