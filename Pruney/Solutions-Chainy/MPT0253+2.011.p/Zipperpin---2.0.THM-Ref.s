%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.liYdajrkRS

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:32 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 145 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  533 (1029 expanded)
%              Number of equality atoms :   51 ( 109 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10 = X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X10 ) @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','30'])).

thf(t48_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_zfmisc_1])).

thf('32',plain,(
    r2_hidden @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X41: $i,X43: $i,X44: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X41 @ X43 ) @ X44 )
      | ~ ( r2_hidden @ X43 @ X44 )
      | ~ ( r2_hidden @ X41 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('38',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B_1 )
    = ( k2_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('44',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','48'])).

thf('50',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('51',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('53',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('56',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_1 ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.liYdajrkRS
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 291 iterations in 0.147s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.61  thf(t2_tarski, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.37/0.61       ( ( A ) = ( B ) ) ))).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         (((X10) = (X9))
% 0.37/0.61          | (r2_hidden @ (sk_C @ X9 @ X10) @ X9)
% 0.37/0.61          | (r2_hidden @ (sk_C @ X9 @ X10) @ X10))),
% 0.37/0.61      inference('cnf', [status(esa)], [t2_tarski])).
% 0.37/0.61  thf(commutativity_k2_tarski, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      (![X23 : $i, X24 : $i]:
% 0.37/0.61         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.61  thf(l51_zfmisc_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (![X39 : $i, X40 : $i]:
% 0.37/0.61         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.37/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['1', '2'])).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (![X39 : $i, X40 : $i]:
% 0.37/0.61         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.37/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.61  thf(t1_boole, axiom,
% 0.37/0.61    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.61  thf('6', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.61  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.61  thf(t39_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      (![X21 : $i, X22 : $i]:
% 0.37/0.61         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 0.37/0.61           = (k2_xboole_0 @ X21 @ X22))),
% 0.37/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.61  thf('10', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.61  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.61  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.61  thf(t22_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (![X17 : $i, X18 : $i]:
% 0.37/0.61         ((k2_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)) = (X17))),
% 0.37/0.61      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['12', '13'])).
% 0.37/0.61  thf(t100_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (![X14 : $i, X15 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X14 @ X15)
% 0.37/0.61           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.61           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.61  thf(d10_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.61  thf('18', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.37/0.61      inference('simplify', [status(thm)], ['17'])).
% 0.37/0.61  thf(t28_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.61  thf('19', plain,
% 0.37/0.61      (![X19 : $i, X20 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.37/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.61  thf('20', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      (![X14 : $i, X15 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X14 @ X15)
% 0.37/0.61           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.37/0.61  thf(d5_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.37/0.61       ( ![D:$i]:
% 0.37/0.61         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.61           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X7 @ X6)
% 0.37/0.61          | ~ (r2_hidden @ X7 @ X5)
% 0.37/0.61          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X7 @ X5)
% 0.37/0.61          | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['23'])).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.37/0.61          | ~ (r2_hidden @ X1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['22', '24'])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.37/0.61          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['16', '25'])).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X7 @ X6)
% 0.37/0.61          | (r2_hidden @ X7 @ X4)
% 0.37/0.61          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.61  thf('28', plain,
% 0.37/0.61      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.37/0.61         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['27'])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('clc', [status(thm)], ['26', '28'])).
% 0.37/0.61  thf('30', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.61      inference('sup-', [status(thm)], ['11', '29'])).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['0', '30'])).
% 0.37/0.61  thf(t48_zfmisc_1, conjecture,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.37/0.61       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.61        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.37/0.61          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.37/0.61  thf('32', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('33', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t38_zfmisc_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.37/0.61       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      (![X41 : $i, X43 : $i, X44 : $i]:
% 0.37/0.61         ((r1_tarski @ (k2_tarski @ X41 @ X43) @ X44)
% 0.37/0.61          | ~ (r2_hidden @ X43 @ X44)
% 0.37/0.61          | ~ (r2_hidden @ X41 @ X44))),
% 0.37/0.61      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.37/0.61  thf('35', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.37/0.61          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.61  thf('36', plain, ((r1_tarski @ (k2_tarski @ sk_C_1 @ sk_A) @ sk_B_1)),
% 0.37/0.61      inference('sup-', [status(thm)], ['32', '35'])).
% 0.37/0.61  thf('37', plain,
% 0.37/0.61      (![X23 : $i, X24 : $i]:
% 0.37/0.61         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.61  thf('38', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B_1)),
% 0.37/0.61      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.61  thf('39', plain,
% 0.37/0.61      (![X19 : $i, X20 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.37/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.61  thf('40', plain,
% 0.37/0.61      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B_1)
% 0.37/0.61         = (k2_tarski @ sk_A @ sk_C_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.61  thf('41', plain,
% 0.37/0.61      (![X14 : $i, X15 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X14 @ X15)
% 0.37/0.61           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B_1)
% 0.37/0.61         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ 
% 0.37/0.61            (k2_tarski @ sk_A @ sk_C_1)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['40', '41'])).
% 0.37/0.61  thf('43', plain,
% 0.37/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.37/0.61  thf('44', plain,
% 0.37/0.61      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.37/0.61         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['27'])).
% 0.37/0.61  thf('45', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.61  thf('46', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.37/0.61          | ~ (r2_hidden @ X1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['22', '24'])).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.61      inference('clc', [status(thm)], ['45', '46'])).
% 0.37/0.61  thf('48', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ~ (r2_hidden @ X0 @ 
% 0.37/0.61            (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['42', '47'])).
% 0.37/0.61  thf('49', plain,
% 0.37/0.61      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B_1) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['31', '48'])).
% 0.37/0.61  thf('50', plain,
% 0.37/0.61      (![X21 : $i, X22 : $i]:
% 0.37/0.61         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 0.37/0.61           = (k2_xboole_0 @ X21 @ X22))),
% 0.37/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.61  thf('51', plain,
% 0.37/0.61      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.37/0.61         = (k2_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_1)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['49', '50'])).
% 0.37/0.61  thf('52', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.61  thf('53', plain,
% 0.37/0.61      (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_1)))),
% 0.37/0.61      inference('demod', [status(thm)], ['51', '52'])).
% 0.37/0.61  thf('54', plain,
% 0.37/0.61      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B_1) != (sk_B_1))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('55', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.61  thf('56', plain,
% 0.37/0.61      (((k2_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_1)) != (sk_B_1))),
% 0.37/0.61      inference('demod', [status(thm)], ['54', '55'])).
% 0.37/0.61  thf('57', plain, ($false),
% 0.37/0.61      inference('simplify_reflect-', [status(thm)], ['53', '56'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
