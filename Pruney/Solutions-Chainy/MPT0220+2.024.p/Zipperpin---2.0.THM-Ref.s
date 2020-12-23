%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5Z3rTo0kwn

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:21 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 160 expanded)
%              Number of leaves         :   22 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  563 (1139 expanded)
%              Number of equality atoms :   66 ( 138 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X49: $i,X50: $i] :
      ( r1_tarski @ ( k1_tarski @ X49 ) @ ( k2_tarski @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16','21','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['5','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','55'])).

thf('57',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5Z3rTo0kwn
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.47/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.71  % Solved by: fo/fo7.sh
% 0.47/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.71  % done 604 iterations in 0.259s
% 0.47/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.71  % SZS output start Refutation
% 0.47/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.71  thf(t14_zfmisc_1, conjecture,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.47/0.71       ( k2_tarski @ A @ B ) ))).
% 0.47/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.71    (~( ![A:$i,B:$i]:
% 0.47/0.71        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.47/0.71          ( k2_tarski @ A @ B ) ) )),
% 0.47/0.71    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.47/0.71  thf('0', plain,
% 0.47/0.71      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.47/0.71         != (k2_tarski @ sk_A @ sk_B))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(t12_zfmisc_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.47/0.71  thf('1', plain,
% 0.47/0.71      (![X49 : $i, X50 : $i]:
% 0.47/0.71         (r1_tarski @ (k1_tarski @ X49) @ (k2_tarski @ X49 @ X50))),
% 0.47/0.71      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.47/0.71  thf(t28_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.47/0.71  thf('2', plain,
% 0.47/0.71      (![X9 : $i, X10 : $i]:
% 0.47/0.71         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.47/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.71  thf('3', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.47/0.71           = (k1_tarski @ X1))),
% 0.47/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.47/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.47/0.71  thf('4', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.71  thf(t48_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.71  thf('5', plain,
% 0.47/0.71      (![X12 : $i, X13 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.47/0.71           = (k3_xboole_0 @ X12 @ X13))),
% 0.47/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.71  thf(d10_xboole_0, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.71  thf('6', plain,
% 0.47/0.71      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.47/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.71  thf('7', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.47/0.71      inference('simplify', [status(thm)], ['6'])).
% 0.47/0.71  thf('8', plain,
% 0.47/0.71      (![X9 : $i, X10 : $i]:
% 0.47/0.71         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.47/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.71  thf('9', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.47/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.71  thf(t100_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.47/0.71  thf('10', plain,
% 0.47/0.71      (![X7 : $i, X8 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X7 @ X8)
% 0.47/0.71           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.47/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.71  thf('11', plain,
% 0.47/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.47/0.71  thf('12', plain,
% 0.47/0.71      (![X7 : $i, X8 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X7 @ X8)
% 0.47/0.71           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.47/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.71  thf(t91_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i]:
% 0.47/0.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.47/0.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.47/0.71  thf('13', plain,
% 0.47/0.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.47/0.71           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.47/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.47/0.71  thf('14', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.71         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.47/0.71           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['12', '13'])).
% 0.47/0.71  thf('15', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.71           = (k5_xboole_0 @ X1 @ 
% 0.47/0.71              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 0.47/0.71      inference('sup+', [status(thm)], ['11', '14'])).
% 0.47/0.71  thf(commutativity_k5_xboole_0, axiom,
% 0.47/0.71    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.47/0.71  thf('16', plain,
% 0.47/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.47/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.47/0.71  thf('17', plain,
% 0.47/0.71      (![X12 : $i, X13 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.47/0.71           = (k3_xboole_0 @ X12 @ X13))),
% 0.47/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.71  thf(t98_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.47/0.71  thf('18', plain,
% 0.47/0.71      (![X19 : $i, X20 : $i]:
% 0.47/0.71         ((k2_xboole_0 @ X19 @ X20)
% 0.47/0.71           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.47/0.71      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.47/0.71  thf('19', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.47/0.71           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.47/0.71  thf('20', plain,
% 0.47/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.47/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.47/0.71  thf('21', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.47/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.47/0.71      inference('demod', [status(thm)], ['19', '20'])).
% 0.47/0.71  thf(t3_boole, axiom,
% 0.47/0.71    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.71  thf('22', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.71  thf('23', plain,
% 0.47/0.71      (![X12 : $i, X13 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.47/0.71           = (k3_xboole_0 @ X12 @ X13))),
% 0.47/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.71  thf('24', plain,
% 0.47/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['22', '23'])).
% 0.47/0.71  thf('25', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.71  thf('26', plain,
% 0.47/0.71      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['24', '25'])).
% 0.47/0.71  thf('27', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.71  thf('28', plain,
% 0.47/0.71      (![X19 : $i, X20 : $i]:
% 0.47/0.71         ((k2_xboole_0 @ X19 @ X20)
% 0.47/0.71           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.47/0.71      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.47/0.71  thf('29', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['27', '28'])).
% 0.47/0.71  thf('30', plain,
% 0.47/0.71      (![X7 : $i, X8 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X7 @ X8)
% 0.47/0.71           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.47/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.71  thf('31', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.47/0.71           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['29', '30'])).
% 0.47/0.71  thf(t7_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.47/0.71  thf('32', plain,
% 0.47/0.71      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.47/0.71      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.47/0.71  thf('33', plain,
% 0.47/0.71      (![X9 : $i, X10 : $i]:
% 0.47/0.71         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.47/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.71  thf('34', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.47/0.71      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.71  thf('35', plain,
% 0.47/0.71      (![X7 : $i, X8 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X7 @ X8)
% 0.47/0.71           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.47/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.71  thf('36', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.47/0.71           = (k5_xboole_0 @ X0 @ X0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['34', '35'])).
% 0.47/0.71  thf('37', plain,
% 0.47/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.47/0.71  thf('38', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.47/0.71           = (k4_xboole_0 @ X0 @ X0))),
% 0.47/0.71      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.71  thf('39', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.47/0.71           = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['31', '38'])).
% 0.47/0.71  thf('40', plain,
% 0.47/0.71      (![X12 : $i, X13 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.47/0.71           = (k3_xboole_0 @ X12 @ X13))),
% 0.47/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.71  thf('41', plain,
% 0.47/0.71      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['24', '25'])).
% 0.47/0.71  thf('42', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.47/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.71  thf('43', plain,
% 0.47/0.71      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.71      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.47/0.71  thf('44', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.47/0.71      inference('demod', [status(thm)], ['26', '43'])).
% 0.54/0.72  thf('45', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.54/0.72           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['15', '16', '21', '44'])).
% 0.54/0.72  thf('46', plain,
% 0.54/0.72      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.54/0.72  thf('47', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.72  thf('48', plain,
% 0.54/0.72      (![X7 : $i, X8 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X7 @ X8)
% 0.54/0.72           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.72  thf('49', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X0 @ X1)
% 0.54/0.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.54/0.72      inference('sup+', [status(thm)], ['47', '48'])).
% 0.54/0.72  thf('50', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['46', '49'])).
% 0.54/0.72  thf('51', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.54/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.54/0.72  thf('52', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['50', '51'])).
% 0.54/0.72  thf('53', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.54/0.72      inference('demod', [status(thm)], ['45', '52'])).
% 0.54/0.72  thf('54', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.54/0.72      inference('sup+', [status(thm)], ['5', '53'])).
% 0.54/0.72  thf('55', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['4', '54'])).
% 0.54/0.72  thf('56', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.54/0.72           = (k2_tarski @ X0 @ X1))),
% 0.54/0.72      inference('sup+', [status(thm)], ['3', '55'])).
% 0.54/0.72  thf('57', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.54/0.72      inference('demod', [status(thm)], ['0', '56'])).
% 0.54/0.72  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.54/0.72  
% 0.54/0.72  % SZS output end Refutation
% 0.54/0.72  
% 0.54/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
