%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zy0MZUj42P

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:19 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 144 expanded)
%              Number of leaves         :   25 (  52 expanded)
%              Depth                    :   22
%              Number of atoms          :  568 (1011 expanded)
%              Number of equality atoms :   53 (  94 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t14_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t14_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X55: $i,X56: $i] :
      ( r1_tarski @ ( k1_tarski @ X55 ) @ ( k2_tarski @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['6','47'])).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['5','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','56'])).

thf('58',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','57'])).

thf('59',plain,(
    $false ),
    inference(simplify,[status(thm)],['58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zy0MZUj42P
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.57/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.74  % Solved by: fo/fo7.sh
% 0.57/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.74  % done 742 iterations in 0.296s
% 0.57/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.74  % SZS output start Refutation
% 0.57/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.57/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.57/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.57/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.74  thf(t14_zfmisc_1, conjecture,
% 0.57/0.74    (![A:$i,B:$i]:
% 0.57/0.74     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.57/0.74       ( k2_tarski @ A @ B ) ))).
% 0.57/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.74    (~( ![A:$i,B:$i]:
% 0.57/0.74        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.57/0.74          ( k2_tarski @ A @ B ) ) )),
% 0.57/0.74    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.57/0.74  thf('0', plain,
% 0.57/0.74      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.57/0.74         != (k2_tarski @ sk_A @ sk_B))),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf(t12_zfmisc_1, axiom,
% 0.57/0.74    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.57/0.74  thf('1', plain,
% 0.57/0.74      (![X55 : $i, X56 : $i]:
% 0.57/0.74         (r1_tarski @ (k1_tarski @ X55) @ (k2_tarski @ X55 @ X56))),
% 0.57/0.74      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.57/0.74  thf(t28_xboole_1, axiom,
% 0.57/0.74    (![A:$i,B:$i]:
% 0.57/0.74     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.57/0.74  thf('2', plain,
% 0.57/0.74      (![X17 : $i, X18 : $i]:
% 0.57/0.74         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.57/0.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.57/0.74  thf('3', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.57/0.74           = (k1_tarski @ X1))),
% 0.57/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.57/0.74  thf(commutativity_k3_xboole_0, axiom,
% 0.57/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.57/0.74  thf('4', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.74  thf(t48_xboole_1, axiom,
% 0.57/0.74    (![A:$i,B:$i]:
% 0.57/0.74     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.57/0.74  thf('5', plain,
% 0.57/0.74      (![X20 : $i, X21 : $i]:
% 0.57/0.74         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.57/0.74           = (k3_xboole_0 @ X20 @ X21))),
% 0.57/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.74  thf(t100_xboole_1, axiom,
% 0.57/0.74    (![A:$i,B:$i]:
% 0.57/0.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.57/0.74  thf('6', plain,
% 0.57/0.74      (![X15 : $i, X16 : $i]:
% 0.57/0.74         ((k4_xboole_0 @ X15 @ X16)
% 0.57/0.74           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.57/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.74  thf(d10_xboole_0, axiom,
% 0.57/0.74    (![A:$i,B:$i]:
% 0.57/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.57/0.74  thf('7', plain,
% 0.57/0.74      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 0.57/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.57/0.74  thf('8', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 0.57/0.74      inference('simplify', [status(thm)], ['7'])).
% 0.57/0.74  thf('9', plain,
% 0.57/0.74      (![X17 : $i, X18 : $i]:
% 0.57/0.74         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.57/0.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.57/0.74  thf('10', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.57/0.74      inference('sup-', [status(thm)], ['8', '9'])).
% 0.57/0.74  thf('11', plain,
% 0.57/0.74      (![X15 : $i, X16 : $i]:
% 0.57/0.74         ((k4_xboole_0 @ X15 @ X16)
% 0.57/0.74           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.57/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.74  thf('12', plain,
% 0.57/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.57/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.57/0.74  thf(t91_xboole_1, axiom,
% 0.57/0.74    (![A:$i,B:$i,C:$i]:
% 0.57/0.74     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.57/0.74       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.57/0.74  thf('13', plain,
% 0.57/0.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.57/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.57/0.74           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.57/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.57/0.74  thf(commutativity_k5_xboole_0, axiom,
% 0.57/0.74    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.57/0.74  thf('14', plain,
% 0.57/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.57/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.57/0.74  thf('15', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.74         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.57/0.74           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.74      inference('sup+', [status(thm)], ['13', '14'])).
% 0.57/0.74  thf('16', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.57/0.74           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.57/0.74      inference('sup+', [status(thm)], ['12', '15'])).
% 0.57/0.74  thf(d3_tarski, axiom,
% 0.57/0.74    (![A:$i,B:$i]:
% 0.57/0.74     ( ( r1_tarski @ A @ B ) <=>
% 0.57/0.74       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.57/0.74  thf('17', plain,
% 0.57/0.74      (![X5 : $i, X7 : $i]:
% 0.57/0.74         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.57/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.74  thf('18', plain,
% 0.57/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.57/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.57/0.74  thf(t1_xboole_0, axiom,
% 0.57/0.74    (![A:$i,B:$i,C:$i]:
% 0.57/0.74     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.57/0.74       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.57/0.74  thf('19', plain,
% 0.57/0.74      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.57/0.74         ((r2_hidden @ X8 @ X9)
% 0.57/0.74          | (r2_hidden @ X8 @ X10)
% 0.57/0.74          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.57/0.74      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.57/0.74  thf('20', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.57/0.74          | (r2_hidden @ X1 @ X0)
% 0.57/0.74          | (r2_hidden @ X1 @ X0))),
% 0.57/0.74      inference('sup-', [status(thm)], ['18', '19'])).
% 0.57/0.74  thf('21', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.57/0.74      inference('simplify', [status(thm)], ['20'])).
% 0.57/0.74  thf('22', plain,
% 0.57/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.57/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.57/0.74  thf('23', plain,
% 0.57/0.74      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.57/0.74         (~ (r2_hidden @ X8 @ X9)
% 0.57/0.74          | ~ (r2_hidden @ X8 @ X10)
% 0.57/0.74          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.57/0.74      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.57/0.74  thf('24', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.57/0.74          | ~ (r2_hidden @ X1 @ X0)
% 0.57/0.74          | ~ (r2_hidden @ X1 @ X0))),
% 0.57/0.74      inference('sup-', [status(thm)], ['22', '23'])).
% 0.57/0.74  thf('25', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         (~ (r2_hidden @ X1 @ X0)
% 0.57/0.74          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.57/0.74      inference('simplify', [status(thm)], ['24'])).
% 0.57/0.74  thf('26', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.57/0.74      inference('clc', [status(thm)], ['21', '25'])).
% 0.57/0.74  thf('27', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.57/0.74      inference('sup-', [status(thm)], ['17', '26'])).
% 0.57/0.74  thf('28', plain,
% 0.57/0.74      (![X5 : $i, X7 : $i]:
% 0.57/0.74         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.57/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.74  thf(t3_boole, axiom,
% 0.57/0.74    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.57/0.74  thf('29', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.57/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.57/0.74  thf('30', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         (~ (r2_hidden @ X1 @ X0)
% 0.57/0.74          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.57/0.74      inference('simplify', [status(thm)], ['24'])).
% 0.57/0.74  thf('31', plain,
% 0.57/0.74      (![X0 : $i]:
% 0.57/0.74         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.57/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.57/0.74  thf('32', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.57/0.74      inference('simplify', [status(thm)], ['31'])).
% 0.57/0.74  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.57/0.74      inference('sup-', [status(thm)], ['28', '32'])).
% 0.57/0.74  thf('34', plain,
% 0.57/0.74      (![X12 : $i, X14 : $i]:
% 0.57/0.74         (((X12) = (X14))
% 0.57/0.74          | ~ (r1_tarski @ X14 @ X12)
% 0.57/0.74          | ~ (r1_tarski @ X12 @ X14))),
% 0.57/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.57/0.74  thf('35', plain,
% 0.57/0.74      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.57/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.57/0.74  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.57/0.74      inference('sup-', [status(thm)], ['27', '35'])).
% 0.57/0.74  thf('37', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.57/0.74      inference('sup-', [status(thm)], ['28', '32'])).
% 0.57/0.74  thf('38', plain,
% 0.57/0.74      (![X17 : $i, X18 : $i]:
% 0.57/0.74         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.57/0.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.57/0.74  thf('39', plain,
% 0.57/0.74      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.57/0.74      inference('sup-', [status(thm)], ['37', '38'])).
% 0.57/0.74  thf('40', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.74  thf('41', plain,
% 0.57/0.74      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.74      inference('sup+', [status(thm)], ['39', '40'])).
% 0.57/0.74  thf('42', plain,
% 0.57/0.74      (![X15 : $i, X16 : $i]:
% 0.57/0.74         ((k4_xboole_0 @ X15 @ X16)
% 0.57/0.74           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.57/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.74  thf('43', plain,
% 0.57/0.74      (![X0 : $i]:
% 0.57/0.74         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.57/0.74      inference('sup+', [status(thm)], ['41', '42'])).
% 0.57/0.74  thf('44', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.57/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.57/0.74  thf('45', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.57/0.74      inference('demod', [status(thm)], ['43', '44'])).
% 0.57/0.74  thf('46', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         ((X1) = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.57/0.74      inference('sup+', [status(thm)], ['36', '45'])).
% 0.57/0.74  thf('47', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.57/0.74      inference('demod', [status(thm)], ['16', '46'])).
% 0.57/0.74  thf('48', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.57/0.74           = (X1))),
% 0.57/0.74      inference('sup+', [status(thm)], ['6', '47'])).
% 0.57/0.74  thf('49', plain,
% 0.57/0.74      (![X20 : $i, X21 : $i]:
% 0.57/0.74         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.57/0.74           = (k3_xboole_0 @ X20 @ X21))),
% 0.57/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.74  thf(t98_xboole_1, axiom,
% 0.57/0.74    (![A:$i,B:$i]:
% 0.57/0.74     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.57/0.74  thf('50', plain,
% 0.57/0.74      (![X25 : $i, X26 : $i]:
% 0.57/0.74         ((k2_xboole_0 @ X25 @ X26)
% 0.57/0.74           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.57/0.74      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.57/0.74  thf('51', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.57/0.74           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.57/0.74      inference('sup+', [status(thm)], ['49', '50'])).
% 0.57/0.74  thf('52', plain,
% 0.57/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.57/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.57/0.74  thf('53', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.57/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.57/0.74      inference('demod', [status(thm)], ['51', '52'])).
% 0.57/0.74  thf('54', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.57/0.74      inference('sup+', [status(thm)], ['48', '53'])).
% 0.57/0.74  thf('55', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.57/0.74      inference('sup+', [status(thm)], ['5', '54'])).
% 0.57/0.74  thf('56', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.57/0.74      inference('sup+', [status(thm)], ['4', '55'])).
% 0.57/0.74  thf('57', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i]:
% 0.57/0.74         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.57/0.74           = (k2_tarski @ X0 @ X1))),
% 0.57/0.74      inference('sup+', [status(thm)], ['3', '56'])).
% 0.57/0.74  thf('58', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.57/0.74      inference('demod', [status(thm)], ['0', '57'])).
% 0.57/0.74  thf('59', plain, ($false), inference('simplify', [status(thm)], ['58'])).
% 0.57/0.74  
% 0.57/0.74  % SZS output end Refutation
% 0.57/0.74  
% 0.57/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
