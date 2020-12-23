%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v8rJmZiiPp

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:10 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 272 expanded)
%              Number of leaves         :   23 (  97 expanded)
%              Depth                    :   20
%              Number of atoms          :  550 (1756 expanded)
%              Number of equality atoms :   73 ( 235 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X37 != X36 )
      | ( r2_hidden @ X37 @ X38 )
      | ( X38
       != ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X36: $i] :
      ( r2_hidden @ X36 @ ( k1_tarski @ X36 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','11','34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('45',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 )
    = ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['45','50'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('53',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','54'])).

thf('56',plain,(
    ! [X36: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X39 @ X38 )
      | ( X39 = X36 )
      | ( X38
       != ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('57',plain,(
    ! [X36: $i,X39: $i] :
      ( ( X39 = X36 )
      | ~ ( r2_hidden @ X39 @ ( k1_tarski @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v8rJmZiiPp
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:43:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.63  % Solved by: fo/fo7.sh
% 0.40/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.63  % done 462 iterations in 0.173s
% 0.40/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.63  % SZS output start Refutation
% 0.40/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.63  thf(d1_tarski, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.40/0.63  thf('0', plain,
% 0.40/0.63      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.40/0.63         (((X37) != (X36))
% 0.40/0.63          | (r2_hidden @ X37 @ X38)
% 0.40/0.63          | ((X38) != (k1_tarski @ X36)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.63  thf('1', plain, (![X36 : $i]: (r2_hidden @ X36 @ (k1_tarski @ X36))),
% 0.40/0.63      inference('simplify', [status(thm)], ['0'])).
% 0.40/0.63  thf(t13_zfmisc_1, conjecture,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.40/0.63         ( k1_tarski @ A ) ) =>
% 0.40/0.63       ( ( A ) = ( B ) ) ))).
% 0.40/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.63    (~( ![A:$i,B:$i]:
% 0.40/0.63        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.40/0.63            ( k1_tarski @ A ) ) =>
% 0.40/0.63          ( ( A ) = ( B ) ) ) )),
% 0.40/0.63    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.40/0.63  thf('2', plain,
% 0.40/0.63      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.40/0.63         = (k1_tarski @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(t98_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.40/0.63  thf('3', plain,
% 0.40/0.63      (![X22 : $i, X23 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ X22 @ X23)
% 0.40/0.63           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.40/0.63  thf(idempotence_k3_xboole_0, axiom,
% 0.40/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.40/0.63  thf('4', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 0.40/0.63      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.40/0.63  thf(t100_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.63  thf('5', plain,
% 0.40/0.63      (![X9 : $i, X10 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X9 @ X10)
% 0.40/0.63           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.63  thf('6', plain,
% 0.40/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.40/0.63  thf(t91_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.40/0.63       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.40/0.63  thf('7', plain,
% 0.40/0.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.63         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.40/0.63           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.40/0.63  thf('8', plain,
% 0.40/0.63      (![X22 : $i, X23 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ X22 @ X23)
% 0.40/0.63           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.40/0.63  thf('9', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.40/0.63           = (k5_xboole_0 @ X1 @ 
% 0.40/0.63              (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 0.40/0.63      inference('sup+', [status(thm)], ['7', '8'])).
% 0.40/0.63  thf('10', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 0.40/0.63           = (k5_xboole_0 @ X0 @ 
% 0.40/0.63              (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))))),
% 0.40/0.63      inference('sup+', [status(thm)], ['6', '9'])).
% 0.40/0.63  thf('11', plain,
% 0.40/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.40/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.63  thf('12', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.40/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.63  thf(t28_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.63  thf('13', plain,
% 0.40/0.63      (![X11 : $i, X12 : $i]:
% 0.40/0.63         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.40/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.63  thf('14', plain,
% 0.40/0.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.63  thf('15', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.63  thf('16', plain,
% 0.40/0.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['14', '15'])).
% 0.40/0.63  thf('17', plain,
% 0.40/0.63      (![X9 : $i, X10 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X9 @ X10)
% 0.40/0.63           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.63  thf('18', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['16', '17'])).
% 0.40/0.63  thf(t5_boole, axiom,
% 0.40/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.63  thf('19', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.40/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.63  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['18', '19'])).
% 0.40/0.63  thf(t51_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.40/0.63       ( A ) ))).
% 0.40/0.63  thf('21', plain,
% 0.40/0.63      (![X16 : $i, X17 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 0.40/0.63           = (X16))),
% 0.40/0.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.40/0.63  thf('22', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['20', '21'])).
% 0.40/0.63  thf('23', plain,
% 0.40/0.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['14', '15'])).
% 0.40/0.63  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.63  thf(t40_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.40/0.63  thf('25', plain,
% 0.40/0.63      (![X14 : $i, X15 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.40/0.63           = (k4_xboole_0 @ X14 @ X15))),
% 0.40/0.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.40/0.63  thf('26', plain,
% 0.40/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['24', '25'])).
% 0.40/0.63  thf('27', plain,
% 0.40/0.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.63  thf('28', plain,
% 0.40/0.63      (![X9 : $i, X10 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X9 @ X10)
% 0.40/0.63           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.63  thf('29', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.40/0.63           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['27', '28'])).
% 0.40/0.63  thf('30', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.40/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.63  thf('31', plain,
% 0.40/0.63      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.63  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.63      inference('demod', [status(thm)], ['26', '31'])).
% 0.40/0.63  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.63  thf('34', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.40/0.63      inference('sup+', [status(thm)], ['32', '33'])).
% 0.40/0.63  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.63      inference('demod', [status(thm)], ['26', '31'])).
% 0.40/0.63  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['18', '19'])).
% 0.40/0.63  thf('37', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.40/0.63      inference('sup+', [status(thm)], ['35', '36'])).
% 0.40/0.63  thf('38', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.40/0.63      inference('demod', [status(thm)], ['10', '11', '34', '37'])).
% 0.40/0.63  thf('39', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.40/0.63           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['3', '38'])).
% 0.40/0.63  thf('40', plain,
% 0.40/0.63      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.40/0.63         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['2', '39'])).
% 0.40/0.63  thf('41', plain,
% 0.40/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.40/0.63  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.63      inference('demod', [status(thm)], ['26', '31'])).
% 0.40/0.63  thf('43', plain,
% 0.40/0.63      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.40/0.63      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.40/0.63  thf('44', plain,
% 0.40/0.63      (![X16 : $i, X17 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 0.40/0.63           = (X16))),
% 0.40/0.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.40/0.63  thf('45', plain,
% 0.40/0.63      (((k2_xboole_0 @ 
% 0.40/0.63         (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ k1_xboole_0)
% 0.40/0.63         = (k1_tarski @ sk_B))),
% 0.40/0.63      inference('sup+', [status(thm)], ['43', '44'])).
% 0.40/0.63  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.63      inference('demod', [status(thm)], ['26', '31'])).
% 0.40/0.63  thf('47', plain,
% 0.40/0.63      (![X16 : $i, X17 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 0.40/0.63           = (X16))),
% 0.40/0.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.40/0.63  thf('48', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['46', '47'])).
% 0.40/0.63  thf('49', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 0.40/0.63      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.40/0.63  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['48', '49'])).
% 0.40/0.63  thf('51', plain,
% 0.40/0.63      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.40/0.63         = (k1_tarski @ sk_B))),
% 0.40/0.63      inference('demod', [status(thm)], ['45', '50'])).
% 0.40/0.63  thf(d4_xboole_0, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.40/0.63       ( ![D:$i]:
% 0.40/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.63           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.40/0.63  thf('52', plain,
% 0.40/0.63      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.40/0.63         (~ (r2_hidden @ X6 @ X5)
% 0.40/0.63          | (r2_hidden @ X6 @ X4)
% 0.40/0.63          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.40/0.63  thf('53', plain,
% 0.40/0.63      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.40/0.63         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.40/0.63      inference('simplify', [status(thm)], ['52'])).
% 0.40/0.63  thf('54', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.40/0.63          | (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['51', '53'])).
% 0.40/0.63  thf('55', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.40/0.63      inference('sup-', [status(thm)], ['1', '54'])).
% 0.40/0.63  thf('56', plain,
% 0.40/0.63      (![X36 : $i, X38 : $i, X39 : $i]:
% 0.40/0.63         (~ (r2_hidden @ X39 @ X38)
% 0.40/0.63          | ((X39) = (X36))
% 0.40/0.63          | ((X38) != (k1_tarski @ X36)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.63  thf('57', plain,
% 0.40/0.63      (![X36 : $i, X39 : $i]:
% 0.40/0.63         (((X39) = (X36)) | ~ (r2_hidden @ X39 @ (k1_tarski @ X36)))),
% 0.40/0.63      inference('simplify', [status(thm)], ['56'])).
% 0.40/0.63  thf('58', plain, (((sk_B) = (sk_A))),
% 0.40/0.63      inference('sup-', [status(thm)], ['55', '57'])).
% 0.40/0.63  thf('59', plain, (((sk_A) != (sk_B))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('60', plain, ($false),
% 0.40/0.63      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.40/0.63  
% 0.40/0.63  % SZS output end Refutation
% 0.40/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
