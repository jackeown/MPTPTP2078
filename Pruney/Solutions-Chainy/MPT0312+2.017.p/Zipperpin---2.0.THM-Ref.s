%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P08CneEosx

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:14 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 118 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  529 ( 876 expanded)
%              Number of equality atoms :   63 ( 102 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t124_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
        = ( k2_zfmisc_1 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
          = ( k2_zfmisc_1 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t124_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X7 @ X6 ) )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('7',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','11','12','15'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('17',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X7 @ X6 ) )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('21',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) )
    = sk_D ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_D @ sk_D ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_D )
    = ( k5_xboole_0 @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('34',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_D @ k1_xboole_0 ) )
    = ( k3_tarski @ ( k2_tarski @ sk_D @ sk_C ) ) ),
    inference('sup+',[status(thm)],['31','35'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('37',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('38',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('39',plain,(
    ! [X8: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ k1_xboole_0 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_D
    = ( k3_tarski @ ( k2_tarski @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = ( k5_xboole_0 @ sk_D @ ( k5_xboole_0 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = ( k5_xboole_0 @ sk_D @ ( k5_xboole_0 @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_C )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['0','18','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P08CneEosx
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.78/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.78/0.99  % Solved by: fo/fo7.sh
% 0.78/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.99  % done 563 iterations in 0.537s
% 0.78/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.78/0.99  % SZS output start Refutation
% 0.78/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.78/0.99  thf(sk_C_type, type, sk_C: $i).
% 0.78/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.78/0.99  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.78/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.78/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.78/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.78/0.99  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.78/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/0.99  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.78/0.99  thf(sk_D_type, type, sk_D: $i).
% 0.78/0.99  thf(t124_zfmisc_1, conjecture,
% 0.78/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.99     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.78/0.99       ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.78/0.99         ( k2_zfmisc_1 @ A @ C ) ) ))).
% 0.78/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.99    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.99        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.78/0.99          ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.78/0.99            ( k2_zfmisc_1 @ A @ C ) ) ) )),
% 0.78/0.99    inference('cnf.neg', [status(esa)], [t124_zfmisc_1])).
% 0.78/0.99  thf('0', plain,
% 0.78/0.99      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D) @ 
% 0.78/0.99         (k2_zfmisc_1 @ sk_B @ sk_C)) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(t12_xboole_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.78/0.99  thf('2', plain,
% 0.78/0.99      (![X6 : $i, X7 : $i]:
% 0.78/0.99         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.78/0.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.78/0.99  thf(l51_zfmisc_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.78/0.99  thf('3', plain,
% 0.78/0.99      (![X45 : $i, X46 : $i]:
% 0.78/0.99         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.78/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.78/0.99  thf('4', plain,
% 0.78/0.99      (![X6 : $i, X7 : $i]:
% 0.78/0.99         (((k3_tarski @ (k2_tarski @ X7 @ X6)) = (X6))
% 0.78/0.99          | ~ (r1_tarski @ X7 @ X6))),
% 0.78/0.99      inference('demod', [status(thm)], ['2', '3'])).
% 0.78/0.99  thf('5', plain, (((k3_tarski @ (k2_tarski @ sk_A @ sk_B)) = (sk_B))),
% 0.78/0.99      inference('sup-', [status(thm)], ['1', '4'])).
% 0.78/0.99  thf(t95_xboole_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( k3_xboole_0 @ A @ B ) =
% 0.78/0.99       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.78/0.99  thf('6', plain,
% 0.78/0.99      (![X16 : $i, X17 : $i]:
% 0.78/0.99         ((k3_xboole_0 @ X16 @ X17)
% 0.78/0.99           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.78/0.99              (k2_xboole_0 @ X16 @ X17)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.78/0.99  thf('7', plain,
% 0.78/0.99      (![X45 : $i, X46 : $i]:
% 0.78/0.99         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.78/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.78/0.99  thf(t91_xboole_1, axiom,
% 0.78/0.99    (![A:$i,B:$i,C:$i]:
% 0.78/0.99     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.78/0.99       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.78/0.99  thf('8', plain,
% 0.78/0.99      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.78/0.99         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.78/0.99           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.78/0.99  thf('9', plain,
% 0.78/0.99      (![X16 : $i, X17 : $i]:
% 0.78/0.99         ((k3_xboole_0 @ X16 @ X17)
% 0.78/0.99           = (k5_xboole_0 @ X16 @ 
% 0.78/0.99              (k5_xboole_0 @ X17 @ (k3_tarski @ (k2_tarski @ X16 @ X17)))))),
% 0.78/0.99      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.78/0.99  thf('10', plain,
% 0.78/0.99      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.78/0.99         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 0.78/0.99      inference('sup+', [status(thm)], ['5', '9'])).
% 0.78/0.99  thf(t92_xboole_1, axiom,
% 0.78/0.99    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.78/0.99  thf('11', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.78/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.78/0.99  thf(commutativity_k5_xboole_0, axiom,
% 0.78/0.99    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.78/0.99  thf('12', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.78/0.99      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.78/0.99  thf('13', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.78/0.99      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.78/0.99  thf(t5_boole, axiom,
% 0.78/0.99    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.78/0.99  thf('14', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.78/0.99      inference('cnf', [status(esa)], [t5_boole])).
% 0.78/0.99  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.78/0.99      inference('sup+', [status(thm)], ['13', '14'])).
% 0.78/0.99  thf('16', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['10', '11', '12', '15'])).
% 0.78/0.99  thf(t123_zfmisc_1, axiom,
% 0.78/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.99     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.78/0.99       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.78/0.99  thf('17', plain,
% 0.78/0.99      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.78/0.99         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 0.78/0.99           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 0.78/0.99              (k2_zfmisc_1 @ X49 @ X50)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.78/0.99  thf('18', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X1 @ X0))
% 0.78/0.99           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ 
% 0.78/0.99              (k2_zfmisc_1 @ sk_B @ X0)))),
% 0.78/0.99      inference('sup+', [status(thm)], ['16', '17'])).
% 0.78/0.99  thf('19', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('20', plain,
% 0.78/0.99      (![X6 : $i, X7 : $i]:
% 0.78/0.99         (((k3_tarski @ (k2_tarski @ X7 @ X6)) = (X6))
% 0.78/0.99          | ~ (r1_tarski @ X7 @ X6))),
% 0.78/0.99      inference('demod', [status(thm)], ['2', '3'])).
% 0.78/0.99  thf('21', plain, (((k3_tarski @ (k2_tarski @ sk_C @ sk_D)) = (sk_D))),
% 0.78/0.99      inference('sup-', [status(thm)], ['19', '20'])).
% 0.78/0.99  thf('22', plain,
% 0.78/0.99      (![X16 : $i, X17 : $i]:
% 0.78/0.99         ((k3_xboole_0 @ X16 @ X17)
% 0.78/0.99           = (k5_xboole_0 @ X16 @ 
% 0.78/0.99              (k5_xboole_0 @ X17 @ (k3_tarski @ (k2_tarski @ X16 @ X17)))))),
% 0.78/0.99      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.78/0.99  thf('23', plain,
% 0.78/0.99      (((k3_xboole_0 @ sk_C @ sk_D)
% 0.78/0.99         = (k5_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_D @ sk_D)))),
% 0.78/0.99      inference('sup+', [status(thm)], ['21', '22'])).
% 0.78/0.99  thf('24', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.78/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.78/0.99  thf('25', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.78/0.99      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.78/0.99  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.78/0.99      inference('sup+', [status(thm)], ['13', '14'])).
% 0.78/0.99  thf('27', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.78/0.99  thf(t100_xboole_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.78/0.99  thf('28', plain,
% 0.78/0.99      (![X4 : $i, X5 : $i]:
% 0.78/0.99         ((k4_xboole_0 @ X4 @ X5)
% 0.78/0.99           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.99  thf('29', plain,
% 0.78/0.99      (((k4_xboole_0 @ sk_C @ sk_D) = (k5_xboole_0 @ sk_C @ sk_C))),
% 0.78/0.99      inference('sup+', [status(thm)], ['27', '28'])).
% 0.78/0.99  thf('30', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.78/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.78/0.99  thf('31', plain, (((k4_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.78/0.99      inference('demod', [status(thm)], ['29', '30'])).
% 0.78/0.99  thf(t39_xboole_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.78/0.99  thf('32', plain,
% 0.78/0.99      (![X9 : $i, X10 : $i]:
% 0.78/0.99         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.78/0.99           = (k2_xboole_0 @ X9 @ X10))),
% 0.78/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.78/0.99  thf('33', plain,
% 0.78/0.99      (![X45 : $i, X46 : $i]:
% 0.78/0.99         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.78/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.78/0.99  thf('34', plain,
% 0.78/0.99      (![X45 : $i, X46 : $i]:
% 0.78/0.99         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.78/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.78/0.99  thf('35', plain,
% 0.78/0.99      (![X9 : $i, X10 : $i]:
% 0.78/0.99         ((k3_tarski @ (k2_tarski @ X9 @ (k4_xboole_0 @ X10 @ X9)))
% 0.78/0.99           = (k3_tarski @ (k2_tarski @ X9 @ X10)))),
% 0.78/0.99      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.78/0.99  thf('36', plain,
% 0.78/0.99      (((k3_tarski @ (k2_tarski @ sk_D @ k1_xboole_0))
% 0.78/0.99         = (k3_tarski @ (k2_tarski @ sk_D @ sk_C)))),
% 0.78/0.99      inference('sup+', [status(thm)], ['31', '35'])).
% 0.78/0.99  thf(t1_boole, axiom,
% 0.78/0.99    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.78/0.99  thf('37', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.78/0.99      inference('cnf', [status(esa)], [t1_boole])).
% 0.78/0.99  thf('38', plain,
% 0.78/0.99      (![X45 : $i, X46 : $i]:
% 0.78/0.99         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.78/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.78/0.99  thf('39', plain,
% 0.78/0.99      (![X8 : $i]: ((k3_tarski @ (k2_tarski @ X8 @ k1_xboole_0)) = (X8))),
% 0.78/0.99      inference('demod', [status(thm)], ['37', '38'])).
% 0.78/0.99  thf('40', plain, (((sk_D) = (k3_tarski @ (k2_tarski @ sk_D @ sk_C)))),
% 0.78/0.99      inference('demod', [status(thm)], ['36', '39'])).
% 0.78/0.99  thf('41', plain,
% 0.78/0.99      (![X16 : $i, X17 : $i]:
% 0.78/0.99         ((k3_xboole_0 @ X16 @ X17)
% 0.78/0.99           = (k5_xboole_0 @ X16 @ 
% 0.78/0.99              (k5_xboole_0 @ X17 @ (k3_tarski @ (k2_tarski @ X16 @ X17)))))),
% 0.78/0.99      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.78/0.99  thf('42', plain,
% 0.78/0.99      (((k3_xboole_0 @ sk_D @ sk_C)
% 0.78/0.99         = (k5_xboole_0 @ sk_D @ (k5_xboole_0 @ sk_C @ sk_D)))),
% 0.78/0.99      inference('sup+', [status(thm)], ['40', '41'])).
% 0.78/0.99  thf('43', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.78/0.99      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.78/0.99  thf('44', plain,
% 0.78/0.99      (((k3_xboole_0 @ sk_D @ sk_C)
% 0.78/0.99         = (k5_xboole_0 @ sk_D @ (k5_xboole_0 @ sk_D @ sk_C)))),
% 0.78/0.99      inference('demod', [status(thm)], ['42', '43'])).
% 0.78/0.99  thf('45', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.78/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.78/0.99  thf('46', plain,
% 0.78/0.99      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.78/0.99         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.78/0.99           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.78/0.99  thf('47', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.78/0.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.78/0.99      inference('sup+', [status(thm)], ['45', '46'])).
% 0.78/0.99  thf('48', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.78/0.99      inference('sup+', [status(thm)], ['13', '14'])).
% 0.78/0.99  thf('49', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.78/0.99      inference('demod', [status(thm)], ['47', '48'])).
% 0.78/0.99  thf('50', plain, (((k3_xboole_0 @ sk_D @ sk_C) = (sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['44', '49'])).
% 0.78/0.99  thf('51', plain,
% 0.78/0.99      (((k2_zfmisc_1 @ sk_A @ sk_C) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['0', '18', '50'])).
% 0.78/0.99  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 0.78/0.99  
% 0.78/0.99  % SZS output end Refutation
% 0.78/0.99  
% 0.78/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
