%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Khxh0ucb5A

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:08 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 127 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  539 ( 915 expanded)
%              Number of equality atoms :   62 ( 106 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t145_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t145_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ( r2_hidden @ X32 @ X31 )
      | ( X31
        = ( k4_xboole_0 @ X31 @ ( k2_tarski @ X30 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('2',plain,(
    sk_C
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','25'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','31'])).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('34',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('40',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','43'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','47'])).

thf('49',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Khxh0ucb5A
% 0.14/0.37  % Computer   : n004.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 20:02:24 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.61/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.80  % Solved by: fo/fo7.sh
% 0.61/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.80  % done 513 iterations in 0.317s
% 0.61/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.80  % SZS output start Refutation
% 0.61/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.80  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.61/0.80  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.61/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.61/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.80  thf(t145_zfmisc_1, conjecture,
% 0.61/0.80    (![A:$i,B:$i,C:$i]:
% 0.61/0.80     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.61/0.80          ( ( C ) !=
% 0.61/0.80            ( k4_xboole_0 @
% 0.61/0.80              ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 0.61/0.80              ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.61/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.80    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.80        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.61/0.80             ( ( C ) !=
% 0.61/0.80               ( k4_xboole_0 @
% 0.61/0.80                 ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 0.61/0.80                 ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.61/0.80    inference('cnf.neg', [status(esa)], [t145_zfmisc_1])).
% 0.61/0.80  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf(t144_zfmisc_1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i]:
% 0.61/0.80     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.61/0.80          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.61/0.80  thf('1', plain,
% 0.61/0.80      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.61/0.80         ((r2_hidden @ X30 @ X31)
% 0.61/0.80          | (r2_hidden @ X32 @ X31)
% 0.61/0.80          | ((X31) = (k4_xboole_0 @ X31 @ (k2_tarski @ X30 @ X32))))),
% 0.61/0.80      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.61/0.80  thf('2', plain,
% 0.61/0.80      (((sk_C)
% 0.61/0.80         != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.61/0.80             (k2_tarski @ sk_A @ sk_B)))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf(commutativity_k2_tarski, axiom,
% 0.61/0.80    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.61/0.80  thf('3', plain,
% 0.61/0.80      (![X24 : $i, X25 : $i]:
% 0.61/0.80         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 0.61/0.80      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.61/0.80  thf(l51_zfmisc_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.80  thf('4', plain,
% 0.61/0.80      (![X28 : $i, X29 : $i]:
% 0.61/0.80         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 0.61/0.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.61/0.80  thf('5', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.80      inference('sup+', [status(thm)], ['3', '4'])).
% 0.61/0.80  thf('6', plain,
% 0.61/0.80      (![X28 : $i, X29 : $i]:
% 0.61/0.80         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 0.61/0.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.61/0.80  thf('7', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.80      inference('sup+', [status(thm)], ['5', '6'])).
% 0.61/0.80  thf(d10_xboole_0, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.80  thf('8', plain,
% 0.61/0.80      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.61/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.80  thf('9', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.61/0.80      inference('simplify', [status(thm)], ['8'])).
% 0.61/0.80  thf(l32_xboole_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.61/0.80  thf('10', plain,
% 0.61/0.80      (![X5 : $i, X7 : $i]:
% 0.61/0.80         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.61/0.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.61/0.80  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.61/0.80  thf(t41_xboole_1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i]:
% 0.61/0.80     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.61/0.80       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.61/0.80  thf('12', plain,
% 0.61/0.80      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.61/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.61/0.80           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.61/0.80  thf('13', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.61/0.80           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['11', '12'])).
% 0.61/0.80  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.61/0.80  thf(idempotence_k2_xboole_0, axiom,
% 0.61/0.80    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.61/0.80  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.61/0.80      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.61/0.80  thf('16', plain,
% 0.61/0.80      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.61/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.61/0.80           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.61/0.80  thf('17', plain,
% 0.61/0.80      (![X5 : $i, X6 : $i]:
% 0.61/0.80         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.61/0.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.61/0.80  thf('18', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.80         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.61/0.80          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['16', '17'])).
% 0.61/0.80  thf('19', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.61/0.80          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['15', '18'])).
% 0.61/0.80  thf('20', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         (((k1_xboole_0) != (k1_xboole_0))
% 0.61/0.80          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['14', '19'])).
% 0.61/0.80  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.61/0.80  thf('22', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.61/0.80      inference('demod', [status(thm)], ['20', '21'])).
% 0.61/0.80  thf('23', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.61/0.80      inference('simplify', [status(thm)], ['22'])).
% 0.61/0.80  thf('24', plain,
% 0.61/0.80      (![X5 : $i, X7 : $i]:
% 0.61/0.80         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.61/0.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.61/0.80  thf('25', plain,
% 0.61/0.80      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['23', '24'])).
% 0.61/0.80  thf('26', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['13', '25'])).
% 0.61/0.80  thf(t98_xboole_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.61/0.80  thf('27', plain,
% 0.61/0.80      (![X19 : $i, X20 : $i]:
% 0.61/0.80         ((k2_xboole_0 @ X19 @ X20)
% 0.61/0.80           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.61/0.80  thf('28', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.61/0.80           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.61/0.80      inference('sup+', [status(thm)], ['26', '27'])).
% 0.61/0.80  thf('29', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.80      inference('sup+', [status(thm)], ['5', '6'])).
% 0.61/0.80  thf(t5_boole, axiom,
% 0.61/0.80    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.61/0.80  thf('30', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.61/0.80      inference('cnf', [status(esa)], [t5_boole])).
% 0.61/0.80  thf('31', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.61/0.80           = (k2_xboole_0 @ X1 @ X0))),
% 0.61/0.80      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.61/0.80  thf('32', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.61/0.80           = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.80      inference('sup+', [status(thm)], ['7', '31'])).
% 0.61/0.80  thf('33', plain,
% 0.61/0.80      (![X19 : $i, X20 : $i]:
% 0.61/0.80         ((k2_xboole_0 @ X19 @ X20)
% 0.61/0.80           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.61/0.80  thf(t92_xboole_1, axiom,
% 0.61/0.80    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.61/0.80  thf('34', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.61/0.80      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.80  thf(t91_xboole_1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i]:
% 0.61/0.80     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.61/0.80       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.61/0.80  thf('35', plain,
% 0.61/0.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.61/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.61/0.80           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.80  thf('36', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.61/0.80           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['34', '35'])).
% 0.61/0.80  thf('37', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.61/0.80      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.80  thf(t95_xboole_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( k3_xboole_0 @ A @ B ) =
% 0.61/0.80       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.61/0.80  thf('38', plain,
% 0.61/0.80      (![X17 : $i, X18 : $i]:
% 0.61/0.80         ((k3_xboole_0 @ X17 @ X18)
% 0.61/0.80           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.61/0.80              (k2_xboole_0 @ X17 @ X18)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.61/0.80  thf('39', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         ((k3_xboole_0 @ X0 @ X0)
% 0.61/0.80           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['37', '38'])).
% 0.61/0.80  thf(idempotence_k3_xboole_0, axiom,
% 0.61/0.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.61/0.80  thf('40', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.61/0.80      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.61/0.80  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.61/0.80      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.61/0.80  thf('42', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.61/0.80      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.61/0.80  thf('43', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['36', '42'])).
% 0.61/0.80  thf('44', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k4_xboole_0 @ X0 @ X1)
% 0.61/0.80           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['33', '43'])).
% 0.61/0.80  thf('45', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1)
% 0.61/0.80           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['32', '44'])).
% 0.61/0.80  thf('46', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k4_xboole_0 @ X0 @ X1)
% 0.61/0.80           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['33', '43'])).
% 0.61/0.80  thf('47', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1)
% 0.61/0.80           = (k4_xboole_0 @ X0 @ X1))),
% 0.61/0.80      inference('demod', [status(thm)], ['45', '46'])).
% 0.61/0.80  thf('48', plain,
% 0.61/0.80      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.61/0.80      inference('demod', [status(thm)], ['2', '47'])).
% 0.61/0.80  thf('49', plain,
% 0.61/0.80      ((((sk_C) != (sk_C))
% 0.61/0.80        | (r2_hidden @ sk_B @ sk_C)
% 0.61/0.80        | (r2_hidden @ sk_A @ sk_C))),
% 0.61/0.80      inference('sup-', [status(thm)], ['1', '48'])).
% 0.61/0.80  thf('50', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 0.61/0.80      inference('simplify', [status(thm)], ['49'])).
% 0.61/0.80  thf('51', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('52', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.61/0.80      inference('clc', [status(thm)], ['50', '51'])).
% 0.61/0.80  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 0.61/0.80  
% 0.61/0.80  % SZS output end Refutation
% 0.61/0.80  
% 0.65/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
