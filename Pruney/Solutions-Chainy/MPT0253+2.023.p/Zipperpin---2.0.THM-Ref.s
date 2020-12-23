%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LM1ePzIk5j

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:33 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 176 expanded)
%              Number of leaves         :   23 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  533 (1330 expanded)
%              Number of equality atoms :   48 ( 126 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

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

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X40: $i,X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X40 @ X42 ) @ X43 )
      | ~ ( r2_hidden @ X42 @ X43 )
      | ~ ( r2_hidden @ X40 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
    = ( k2_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('34',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','35'])).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('41',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','46'])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) )
    = sk_B ),
    inference('sup+',[status(thm)],['0','47'])).

thf('49',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('51',plain,(
    ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) )
 != sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LM1ePzIk5j
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.51/1.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.51/1.71  % Solved by: fo/fo7.sh
% 1.51/1.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.71  % done 2419 iterations in 1.249s
% 1.51/1.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.51/1.71  % SZS output start Refutation
% 1.51/1.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.51/1.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.51/1.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.51/1.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.51/1.71  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.51/1.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.51/1.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.51/1.71  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.51/1.71  thf(t39_xboole_1, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.51/1.71  thf('0', plain,
% 1.51/1.71      (![X20 : $i, X21 : $i]:
% 1.51/1.71         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 1.51/1.71           = (k2_xboole_0 @ X20 @ X21))),
% 1.51/1.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.51/1.71  thf(t48_zfmisc_1, conjecture,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 1.51/1.71       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 1.51/1.71  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.71    (~( ![A:$i,B:$i,C:$i]:
% 1.51/1.71        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 1.51/1.71          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 1.51/1.71    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 1.51/1.71  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('2', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(t38_zfmisc_1, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.51/1.71       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.51/1.71  thf('3', plain,
% 1.51/1.71      (![X40 : $i, X42 : $i, X43 : $i]:
% 1.51/1.71         ((r1_tarski @ (k2_tarski @ X40 @ X42) @ X43)
% 1.51/1.71          | ~ (r2_hidden @ X42 @ X43)
% 1.51/1.71          | ~ (r2_hidden @ X40 @ X43))),
% 1.51/1.71      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.51/1.71  thf('4', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         (~ (r2_hidden @ X0 @ sk_B)
% 1.51/1.71          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_1) @ sk_B))),
% 1.51/1.71      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.71  thf('5', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)),
% 1.51/1.71      inference('sup-', [status(thm)], ['1', '4'])).
% 1.51/1.71  thf(t28_xboole_1, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.51/1.71  thf('6', plain,
% 1.51/1.71      (![X18 : $i, X19 : $i]:
% 1.51/1.71         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.51/1.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.51/1.71  thf('7', plain,
% 1.51/1.71      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)
% 1.51/1.71         = (k2_tarski @ sk_A @ sk_C_1))),
% 1.51/1.71      inference('sup-', [status(thm)], ['5', '6'])).
% 1.51/1.71  thf(t100_xboole_1, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.51/1.71  thf('8', plain,
% 1.51/1.71      (![X16 : $i, X17 : $i]:
% 1.51/1.71         ((k4_xboole_0 @ X16 @ X17)
% 1.51/1.71           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.51/1.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.51/1.71  thf('9', plain,
% 1.51/1.71      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)
% 1.51/1.71         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ 
% 1.51/1.71            (k2_tarski @ sk_A @ sk_C_1)))),
% 1.51/1.71      inference('sup+', [status(thm)], ['7', '8'])).
% 1.51/1.71  thf(d3_tarski, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( r1_tarski @ A @ B ) <=>
% 1.51/1.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.51/1.71  thf('10', plain,
% 1.51/1.71      (![X3 : $i, X5 : $i]:
% 1.51/1.71         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.51/1.71      inference('cnf', [status(esa)], [d3_tarski])).
% 1.51/1.71  thf(d10_xboole_0, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.51/1.71  thf('11', plain,
% 1.51/1.71      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 1.51/1.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.71  thf('12', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 1.51/1.71      inference('simplify', [status(thm)], ['11'])).
% 1.51/1.71  thf('13', plain,
% 1.51/1.71      (![X18 : $i, X19 : $i]:
% 1.51/1.71         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.51/1.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.51/1.71  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.51/1.71      inference('sup-', [status(thm)], ['12', '13'])).
% 1.51/1.71  thf('15', plain,
% 1.51/1.71      (![X16 : $i, X17 : $i]:
% 1.51/1.71         ((k4_xboole_0 @ X16 @ X17)
% 1.51/1.71           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.51/1.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.51/1.71  thf('16', plain,
% 1.51/1.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.51/1.71      inference('sup+', [status(thm)], ['14', '15'])).
% 1.51/1.71  thf(d5_xboole_0, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.51/1.71       ( ![D:$i]:
% 1.51/1.71         ( ( r2_hidden @ D @ C ) <=>
% 1.51/1.71           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.51/1.71  thf('17', plain,
% 1.51/1.71      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.51/1.71         (~ (r2_hidden @ X10 @ X9)
% 1.51/1.71          | (r2_hidden @ X10 @ X7)
% 1.51/1.71          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.51/1.71      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.51/1.71  thf('18', plain,
% 1.51/1.71      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.51/1.71         ((r2_hidden @ X10 @ X7)
% 1.51/1.71          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.51/1.71      inference('simplify', [status(thm)], ['17'])).
% 1.51/1.71  thf('19', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 1.51/1.71      inference('sup-', [status(thm)], ['16', '18'])).
% 1.51/1.71  thf('20', plain,
% 1.51/1.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.51/1.71      inference('sup+', [status(thm)], ['14', '15'])).
% 1.51/1.71  thf('21', plain,
% 1.51/1.71      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.51/1.71         (~ (r2_hidden @ X10 @ X9)
% 1.51/1.71          | ~ (r2_hidden @ X10 @ X8)
% 1.51/1.71          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.51/1.71      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.51/1.71  thf('22', plain,
% 1.51/1.71      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.51/1.71         (~ (r2_hidden @ X10 @ X8)
% 1.51/1.71          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.51/1.71      inference('simplify', [status(thm)], ['21'])).
% 1.51/1.71  thf('23', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 1.51/1.71          | ~ (r2_hidden @ X1 @ X0))),
% 1.51/1.71      inference('sup-', [status(thm)], ['20', '22'])).
% 1.51/1.71  thf('24', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 1.51/1.71      inference('clc', [status(thm)], ['19', '23'])).
% 1.51/1.71  thf('25', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 1.51/1.71      inference('sup-', [status(thm)], ['10', '24'])).
% 1.51/1.71  thf('26', plain,
% 1.51/1.71      (![X18 : $i, X19 : $i]:
% 1.51/1.71         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.51/1.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.51/1.71  thf('27', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 1.51/1.71           = (k5_xboole_0 @ X1 @ X1))),
% 1.51/1.71      inference('sup-', [status(thm)], ['25', '26'])).
% 1.51/1.71  thf('28', plain,
% 1.51/1.71      (![X16 : $i, X17 : $i]:
% 1.51/1.71         ((k4_xboole_0 @ X16 @ X17)
% 1.51/1.71           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.51/1.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.51/1.71  thf('29', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 1.51/1.71           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0)))),
% 1.51/1.71      inference('sup+', [status(thm)], ['27', '28'])).
% 1.51/1.71  thf(t91_xboole_1, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.51/1.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.51/1.71  thf('30', plain,
% 1.51/1.71      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.51/1.71         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 1.51/1.71           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 1.51/1.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.51/1.71  thf('31', plain,
% 1.51/1.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.51/1.71      inference('sup+', [status(thm)], ['14', '15'])).
% 1.51/1.71  thf(t98_xboole_1, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.51/1.71  thf('32', plain,
% 1.51/1.71      (![X27 : $i, X28 : $i]:
% 1.51/1.71         ((k2_xboole_0 @ X27 @ X28)
% 1.51/1.71           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 1.51/1.71      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.51/1.71  thf('33', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         ((k2_xboole_0 @ X0 @ X0)
% 1.51/1.71           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.51/1.71      inference('sup+', [status(thm)], ['31', '32'])).
% 1.51/1.71  thf(idempotence_k2_xboole_0, axiom,
% 1.51/1.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.51/1.71  thf('34', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ X12) = (X12))),
% 1.51/1.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.51/1.71  thf('35', plain,
% 1.51/1.71      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.51/1.71      inference('demod', [status(thm)], ['33', '34'])).
% 1.51/1.71  thf('36', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 1.51/1.71           = (k5_xboole_0 @ X0 @ X0))),
% 1.51/1.71      inference('demod', [status(thm)], ['29', '30', '35'])).
% 1.51/1.71  thf('37', plain,
% 1.51/1.71      (![X27 : $i, X28 : $i]:
% 1.51/1.71         ((k2_xboole_0 @ X27 @ X28)
% 1.51/1.71           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 1.51/1.71      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.51/1.71  thf('38', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 1.51/1.71           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.51/1.71      inference('sup+', [status(thm)], ['36', '37'])).
% 1.51/1.71  thf('39', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 1.51/1.71      inference('sup-', [status(thm)], ['10', '24'])).
% 1.51/1.71  thf('40', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 1.51/1.71      inference('sup-', [status(thm)], ['10', '24'])).
% 1.51/1.71  thf('41', plain,
% 1.51/1.71      (![X13 : $i, X15 : $i]:
% 1.51/1.71         (((X13) = (X15))
% 1.51/1.71          | ~ (r1_tarski @ X15 @ X13)
% 1.51/1.71          | ~ (r1_tarski @ X13 @ X15))),
% 1.51/1.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.71  thf('42', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ X1 @ X1))
% 1.51/1.71          | ((X0) = (k5_xboole_0 @ X1 @ X1)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['40', '41'])).
% 1.51/1.71  thf('43', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X1) = (k5_xboole_0 @ X0 @ X0))),
% 1.51/1.71      inference('sup-', [status(thm)], ['39', '42'])).
% 1.51/1.71  thf('44', plain,
% 1.51/1.71      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.51/1.71      inference('demod', [status(thm)], ['33', '34'])).
% 1.51/1.71  thf('45', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((X1) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.51/1.71      inference('sup+', [status(thm)], ['43', '44'])).
% 1.51/1.71  thf('46', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 1.51/1.71      inference('demod', [status(thm)], ['38', '45'])).
% 1.51/1.71  thf('47', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         ((k2_xboole_0 @ X0 @ 
% 1.51/1.71           (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)) = (X0))),
% 1.51/1.71      inference('sup+', [status(thm)], ['9', '46'])).
% 1.51/1.71  thf('48', plain,
% 1.51/1.71      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1)) = (sk_B))),
% 1.51/1.71      inference('sup+', [status(thm)], ['0', '47'])).
% 1.51/1.71  thf('49', plain,
% 1.51/1.71      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B) != (sk_B))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(commutativity_k2_xboole_0, axiom,
% 1.51/1.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.51/1.71  thf('50', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.51/1.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.51/1.71  thf('51', plain,
% 1.51/1.71      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1)) != (sk_B))),
% 1.51/1.71      inference('demod', [status(thm)], ['49', '50'])).
% 1.51/1.71  thf('52', plain, ($false),
% 1.51/1.71      inference('simplify_reflect-', [status(thm)], ['48', '51'])).
% 1.51/1.71  
% 1.51/1.71  % SZS output end Refutation
% 1.51/1.71  
% 1.51/1.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
