%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RgcGyAFi2c

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:40 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 292 expanded)
%              Number of leaves         :   26 (  96 expanded)
%              Depth                    :   19
%              Number of atoms          :  563 (2306 expanded)
%              Number of equality atoms :   67 ( 328 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('3',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X50 ) @ X51 )
      | ( r2_hidden @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['1','10'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('12',plain,(
    ! [X55: $i,X57: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X55 ) @ X57 )
      | ~ ( r2_hidden @ X55 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('13',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['15','18'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['15','18'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['15','18'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('31',plain,(
    ! [X54: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X54 ) )
      = X54 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('32',plain,
    ( ( k3_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['15','18'])).

thf('34',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r2_hidden @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X55: $i,X57: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X55 ) @ X57 )
      | ~ ( r2_hidden @ X55 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['15','18'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['32','33'])).

thf('42',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('44',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B = sk_C )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['26','45'])).

thf('47',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('51',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('52',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('59',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('60',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','63'])).

thf('65',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['25','50','64'])).

thf('66',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RgcGyAFi2c
% 0.11/0.32  % Computer   : n014.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 18:10:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 134 iterations in 0.056s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.51  thf(d10_xboole_0, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.19/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.51  thf('1', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.19/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.51  thf(t44_zfmisc_1, conjecture,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.19/0.51          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.51          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.51        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.19/0.51             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.51             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.19/0.51  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(l27_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (![X50 : $i, X51 : $i]:
% 0.19/0.51         ((r1_xboole_0 @ (k1_tarski @ X50) @ X51) | (r2_hidden @ X50 @ X51))),
% 0.19/0.51      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ X0)
% 0.19/0.51          | (r2_hidden @ sk_A @ X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.19/0.51  thf(t7_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.51  thf(t67_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.19/0.51         ( r1_xboole_0 @ B @ C ) ) =>
% 0.19/0.51       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.51         (((X11) = (k1_xboole_0))
% 0.19/0.51          | ~ (r1_tarski @ X11 @ X12)
% 0.19/0.51          | ~ (r1_tarski @ X11 @ X13)
% 0.19/0.51          | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.19/0.51      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.19/0.51          | ~ (r1_tarski @ X1 @ X2)
% 0.19/0.51          | ((X1) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ sk_A @ X0)
% 0.19/0.51          | ((sk_B) = (k1_xboole_0))
% 0.19/0.51          | ~ (r1_tarski @ sk_B @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['4', '7'])).
% 0.19/0.51  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      (![X0 : $i]: ((r2_hidden @ sk_A @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.19/0.51      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.19/0.51  thf('11', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.19/0.51      inference('sup-', [status(thm)], ['1', '10'])).
% 0.19/0.51  thf(t37_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      (![X55 : $i, X57 : $i]:
% 0.19/0.51         ((r1_tarski @ (k1_tarski @ X55) @ X57) | ~ (r2_hidden @ X55 @ X57))),
% 0.19/0.51      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.19/0.51  thf('13', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.19/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.51  thf('14', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('15', plain, ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_B)),
% 0.19/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      (![X6 : $i, X8 : $i]:
% 0.19/0.51         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.19/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.19/0.51          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.51  thf('19', plain, (((k2_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['15', '18'])).
% 0.19/0.51  thf(t95_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( k3_xboole_0 @ A @ B ) =
% 0.19/0.51       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      (![X20 : $i, X21 : $i]:
% 0.19/0.51         ((k3_xboole_0 @ X20 @ X21)
% 0.19/0.51           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.19/0.51              (k2_xboole_0 @ X20 @ X21)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.19/0.51  thf(t91_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.51       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.19/0.51  thf('21', plain,
% 0.19/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.51         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.19/0.51           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.19/0.51  thf('22', plain,
% 0.19/0.51      (![X20 : $i, X21 : $i]:
% 0.19/0.51         ((k3_xboole_0 @ X20 @ X21)
% 0.19/0.51           = (k5_xboole_0 @ X20 @ 
% 0.19/0.51              (k5_xboole_0 @ X21 @ (k2_xboole_0 @ X20 @ X21))))),
% 0.19/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.19/0.51         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_B)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['19', '22'])).
% 0.19/0.51  thf(commutativity_k5_xboole_0, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.19/0.51  thf('24', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.19/0.51         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.19/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.19/0.51  thf('26', plain, (((k2_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['15', '18'])).
% 0.19/0.51  thf('27', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ X0)
% 0.19/0.51          | (r2_hidden @ sk_A @ X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.19/0.51  thf('28', plain, (((k2_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['15', '18'])).
% 0.19/0.51  thf('29', plain,
% 0.19/0.51      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.19/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.51  thf('30', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t31_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.19/0.51  thf('31', plain, (![X54 : $i]: ((k3_tarski @ (k1_tarski @ X54)) = (X54))),
% 0.19/0.51      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.19/0.51  thf('32', plain, (((k3_tarski @ (k2_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.19/0.51      inference('sup+', [status(thm)], ['30', '31'])).
% 0.19/0.51  thf('33', plain, (((k2_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['15', '18'])).
% 0.19/0.51  thf('34', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['32', '33'])).
% 0.19/0.51  thf('35', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r1_xboole_0 @ sk_B @ X0) | (r2_hidden @ (k3_tarski @ sk_B) @ X0))),
% 0.19/0.51      inference('demod', [status(thm)], ['29', '34'])).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      (![X55 : $i, X57 : $i]:
% 0.19/0.51         ((r1_tarski @ (k1_tarski @ X55) @ X57) | ~ (r2_hidden @ X55 @ X57))),
% 0.19/0.51      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r1_xboole_0 @ sk_B @ X0)
% 0.19/0.51          | (r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B)) @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.51  thf('38', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('39', plain, (((k2_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['15', '18'])).
% 0.19/0.51  thf('40', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.51  thf('41', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['32', '33'])).
% 0.19/0.51  thf('42', plain, (((k1_tarski @ (k3_tarski @ sk_B)) = (sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | (r1_tarski @ sk_B @ X0))),
% 0.19/0.51      inference('demod', [status(thm)], ['37', '42'])).
% 0.19/0.51  thf(t12_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.19/0.51  thf('44', plain,
% 0.19/0.51      (![X9 : $i, X10 : $i]:
% 0.19/0.51         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.19/0.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.51  thf('45', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r1_xboole_0 @ sk_B @ X0) | ((k2_xboole_0 @ sk_B @ X0) = (X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.51  thf('46', plain, ((((sk_B) = (sk_C)) | (r1_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.51      inference('sup+', [status(thm)], ['26', '45'])).
% 0.19/0.51  thf('47', plain, (((sk_B) != (sk_C))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('48', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.19/0.51      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.19/0.51  thf(d7_xboole_0, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.19/0.51       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.51  thf('49', plain,
% 0.19/0.51      (![X2 : $i, X3 : $i]:
% 0.19/0.51         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.19/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.51  thf('50', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.51  thf(t92_xboole_1, axiom,
% 0.19/0.51    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.51  thf('51', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.51  thf('52', plain,
% 0.19/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.51         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.19/0.51           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.19/0.51  thf('53', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.19/0.51           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['51', '52'])).
% 0.19/0.51  thf('54', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.19/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.51  thf('55', plain,
% 0.19/0.51      (![X9 : $i, X10 : $i]:
% 0.19/0.51         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.19/0.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.51  thf('56', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.19/0.51  thf('57', plain,
% 0.19/0.51      (![X20 : $i, X21 : $i]:
% 0.19/0.51         ((k3_xboole_0 @ X20 @ X21)
% 0.19/0.51           = (k5_xboole_0 @ X20 @ 
% 0.19/0.51              (k5_xboole_0 @ X21 @ (k2_xboole_0 @ X20 @ X21))))),
% 0.19/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.51  thf('58', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((k3_xboole_0 @ X0 @ X0)
% 0.19/0.51           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['56', '57'])).
% 0.19/0.51  thf(idempotence_k3_xboole_0, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.51  thf('59', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.19/0.51      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.19/0.51  thf('60', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.51  thf('61', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.51      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.19/0.51  thf('62', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.51  thf('63', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.51  thf('64', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['53', '63'])).
% 0.19/0.51  thf('65', plain, (((k1_xboole_0) = (sk_C))),
% 0.19/0.51      inference('demod', [status(thm)], ['25', '50', '64'])).
% 0.19/0.51  thf('66', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('67', plain, ($false),
% 0.19/0.51      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
