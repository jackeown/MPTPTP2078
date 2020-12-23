%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X6ZsWoSwkH

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 525 expanded)
%              Number of leaves         :   31 ( 189 expanded)
%              Depth                    :   17
%              Number of atoms          :  568 (4030 expanded)
%              Number of equality atoms :   63 ( 512 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
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
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('11',plain,(
    ! [X57: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X57 ) )
      = X57 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['23','32','33'])).

thf('40',plain,
    ( ( r2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('43',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X53 ) @ X54 )
      | ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['23','32','33'])).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 )
      | ( r1_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('50',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X50 ) @ X52 )
      | ~ ( r2_hidden @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r2_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r2_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_xboole_0 @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['42','53'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('55',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X13 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('56',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X6ZsWoSwkH
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 401 iterations in 0.108s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.56  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(t66_zfmisc_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.20/0.56          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i]:
% 0.20/0.56        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.20/0.56             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t95_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k3_xboole_0 @ A @ B ) =
% 0.20/0.56       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X20 : $i, X21 : $i]:
% 0.20/0.56         ((k3_xboole_0 @ X20 @ X21)
% 0.20/0.56           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.20/0.56              (k2_xboole_0 @ X20 @ X21)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.20/0.56  thf(t91_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.56       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.20/0.56           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X20 : $i, X21 : $i]:
% 0.20/0.56         ((k3_xboole_0 @ X20 @ X21)
% 0.20/0.56           = (k5_xboole_0 @ X20 @ 
% 0.20/0.56              (k5_xboole_0 @ X21 @ (k2_xboole_0 @ X20 @ X21))))),
% 0.20/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf(t92_xboole_1, axiom,
% 0.20/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.56  thf('4', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.20/0.56           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X20 : $i, X21 : $i]:
% 0.20/0.56         ((k3_xboole_0 @ X20 @ X21)
% 0.20/0.56           = (k5_xboole_0 @ X20 @ 
% 0.20/0.56              (k5_xboole_0 @ X21 @ (k2_xboole_0 @ X20 @ X21))))),
% 0.20/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 0.20/0.56           = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.56  thf(t69_enumset1, axiom,
% 0.20/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.20/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.56  thf(t31_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.56  thf('11', plain, (![X57 : $i]: ((k3_tarski @ (k1_tarski @ X57)) = (X57))),
% 0.20/0.56      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.56  thf('12', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.56  thf(l51_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X55 : $i, X56 : $i]:
% 0.20/0.56         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 0.20/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.56  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.56  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.56  thf('15', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.56  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['9', '14', '15'])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['6', '16'])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.20/0.56           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['3', '17'])).
% 0.20/0.56  thf(t100_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X4 : $i, X5 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X4 @ X5)
% 0.20/0.56           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.20/0.56           = (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['6', '16'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k2_xboole_0 @ X1 @ X0)
% 0.20/0.56           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.56         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['0', '22'])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.20/0.56           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.56  thf('25', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.20/0.56           = (k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['6', '16'])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.20/0.56           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.56  thf(t5_boole, axiom,
% 0.20/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.56  thf('29', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.20/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['6', '16'])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.56  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['9', '14', '15'])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['23', '32', '33'])).
% 0.20/0.56  thf(t7_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.20/0.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.56  thf(d8_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.56       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      (![X0 : $i, X2 : $i]:
% 0.20/0.56         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 0.20/0.56          | (r2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (((r2_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.57        | ((sk_A) = (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['34', '37'])).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)], ['23', '32', '33'])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      (((r2_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.57        | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.57  thf('41', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('42', plain, ((r2_xboole_0 @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.57      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.20/0.57  thf(l27_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.57  thf('43', plain,
% 0.20/0.57      (![X53 : $i, X54 : $i]:
% 0.20/0.57         ((r1_xboole_0 @ (k1_tarski @ X53) @ X54) | (r2_hidden @ X53 @ X54))),
% 0.20/0.57      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.57  thf('44', plain,
% 0.20/0.57      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)], ['23', '32', '33'])).
% 0.20/0.57  thf('45', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.20/0.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.57  thf(t63_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.57       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.57  thf('46', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.57         (~ (r1_tarski @ X9 @ X10)
% 0.20/0.57          | ~ (r1_xboole_0 @ X10 @ X11)
% 0.20/0.57          | (r1_xboole_0 @ X9 @ X11))),
% 0.20/0.57      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.20/0.57  thf('47', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         ((r1_xboole_0 @ X1 @ X2)
% 0.20/0.57          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.20/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.57  thf('48', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0) | (r1_xboole_0 @ sk_A @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['44', '47'])).
% 0.20/0.57  thf('49', plain,
% 0.20/0.57      (![X0 : $i]: ((r2_hidden @ sk_B @ X0) | (r1_xboole_0 @ sk_A @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['43', '48'])).
% 0.20/0.57  thf(l1_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.57  thf('50', plain,
% 0.20/0.57      (![X50 : $i, X52 : $i]:
% 0.20/0.57         ((r1_tarski @ (k1_tarski @ X50) @ X52) | ~ (r2_hidden @ X50 @ X52))),
% 0.20/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r1_xboole_0 @ sk_A @ X0) | (r1_tarski @ (k1_tarski @ sk_B) @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.57  thf(t60_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      (![X7 : $i, X8 : $i]:
% 0.20/0.57         (~ (r1_tarski @ X7 @ X8) | ~ (r2_xboole_0 @ X8 @ X7))),
% 0.20/0.57      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.20/0.57  thf('53', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r1_xboole_0 @ sk_A @ X0) | ~ (r2_xboole_0 @ X0 @ (k1_tarski @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.57  thf('54', plain, ((r1_xboole_0 @ sk_A @ sk_A)),
% 0.20/0.57      inference('sup-', [status(thm)], ['42', '53'])).
% 0.20/0.57  thf(t66_xboole_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.20/0.57       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.57  thf('55', plain,
% 0.20/0.57      (![X13 : $i]: (((X13) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X13 @ X13))),
% 0.20/0.57      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.20/0.57  thf('56', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.57  thf('57', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('58', plain, ($false),
% 0.20/0.57      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
