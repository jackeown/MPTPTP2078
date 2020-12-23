%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ApF7PnmkzL

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 180 expanded)
%              Number of leaves         :   22 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  543 (1334 expanded)
%              Number of equality atoms :   50 ( 126 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

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
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','25'])).

thf('27',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29','30','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,
    ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','52'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29','30','38'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('55',plain,(
    ! [X19: $i] :
      ( r1_xboole_0 @ X19 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['53','54','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ApF7PnmkzL
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:46:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 229 iterations in 0.092s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(t77_xboole_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.55          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.55        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.55             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.21/0.55  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t7_xboole_0, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.55  thf(t4_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.21/0.55          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf(t47_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X12 : $i, X13 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.21/0.55           = (k4_xboole_0 @ X12 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.55           = (k4_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_C_1) @ k1_xboole_0)
% 0.21/0.55         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['5', '8'])).
% 0.21/0.55  thf(t49_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.21/0.55       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.21/0.55           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.21/0.55      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.55  thf(t3_boole, axiom,
% 0.21/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.55  thf('11', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.21/0.55           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.21/0.55      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_B_1 @ sk_C_1)
% 0.21/0.55         = (k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.21/0.55  thf('14', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.55  thf(t48_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.55           = (k3_xboole_0 @ X14 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf(t2_boole, axiom,
% 0.21/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.55  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.21/0.55           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.21/0.55      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.55  thf(l32_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.21/0.55          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X1 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.55          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['18', '21'])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.55          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.21/0.55      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      ((r1_tarski @ (k3_xboole_0 @ sk_B_1 @ sk_C_1) @ 
% 0.21/0.55        (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['13', '25'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X7 : $i, X9 : $i]:
% 0.21/0.55         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_C_1) @ 
% 0.21/0.55         (k4_xboole_0 @ sk_C_1 @ sk_A)) = (k1_xboole_0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.21/0.55           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.21/0.55      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.55           = (k3_xboole_0 @ X14 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.55  thf('31', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X7 : $i, X9 : $i]:
% 0.21/0.55         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.55  thf('33', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.55           = (k3_xboole_0 @ X14 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.55  thf('36', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf('38', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.55  thf('39', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.55      inference('demod', [status(thm)], ['28', '29', '30', '38'])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X2 @ X3)
% 0.21/0.55          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.55          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['40', '41'])).
% 0.21/0.55  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.55           = (k3_xboole_0 @ X14 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.55  thf('46', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.55  thf('47', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.21/0.55          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.55          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['47', '50'])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.55          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['42', '51'])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      ((~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_A) @ k1_xboole_0)
% 0.21/0.55        | (r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['39', '52'])).
% 0.21/0.55  thf('54', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.55      inference('demod', [status(thm)], ['28', '29', '30', '38'])).
% 0.21/0.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.55  thf('55', plain, (![X19 : $i]: (r1_xboole_0 @ X19 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X2 @ X3)
% 0.21/0.55          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.55          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.55  thf('59', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.55      inference('sup-', [status(thm)], ['55', '58'])).
% 0.21/0.55  thf('60', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.55      inference('demod', [status(thm)], ['53', '54', '59'])).
% 0.21/0.55  thf('61', plain, ($false), inference('demod', [status(thm)], ['0', '60'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
