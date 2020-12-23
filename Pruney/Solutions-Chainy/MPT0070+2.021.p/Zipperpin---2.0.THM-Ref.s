%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wgUUyKfvkC

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:35 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 113 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  573 ( 801 expanded)
%              Number of equality atoms :   57 (  77 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) )
    = sk_C ),
    inference('sup+',[status(thm)],['5','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('34',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('46',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('49',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','54'])).

thf('56',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['34','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wgUUyKfvkC
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:48:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.53  % Solved by: fo/fo7.sh
% 0.37/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.53  % done 259 iterations in 0.086s
% 0.37/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.53  % SZS output start Refutation
% 0.37/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.53  thf(t63_xboole_1, conjecture,
% 0.37/0.53    (![A:$i,B:$i,C:$i]:
% 0.37/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.37/0.53       ( r1_xboole_0 @ A @ C ) ))).
% 0.37/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.53        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.37/0.53          ( r1_xboole_0 @ A @ C ) ) )),
% 0.37/0.53    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.37/0.53  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('1', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf(symmetry_r1_xboole_0, axiom,
% 0.37/0.53    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.37/0.53  thf('2', plain,
% 0.37/0.53      (![X5 : $i, X6 : $i]:
% 0.37/0.53         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.37/0.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.53  thf('3', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.37/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.53  thf(d7_xboole_0, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.53       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.53  thf('4', plain,
% 0.37/0.53      (![X2 : $i, X3 : $i]:
% 0.37/0.53         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.37/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.53  thf('5', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.53  thf(t48_xboole_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.53  thf('6', plain,
% 0.37/0.53      (![X19 : $i, X20 : $i]:
% 0.37/0.53         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.37/0.53           = (k3_xboole_0 @ X19 @ X20))),
% 0.37/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.53  thf(t39_xboole_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.53  thf('7', plain,
% 0.37/0.53      (![X13 : $i, X14 : $i]:
% 0.37/0.53         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.37/0.53           = (k2_xboole_0 @ X13 @ X14))),
% 0.37/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.53  thf('8', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.53           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.37/0.53      inference('sup+', [status(thm)], ['6', '7'])).
% 0.37/0.53  thf(commutativity_k2_xboole_0, axiom,
% 0.37/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.37/0.53  thf('9', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.53  thf('10', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.53  thf('11', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.37/0.53           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.53      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.37/0.53  thf(t36_xboole_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.53  thf('12', plain,
% 0.37/0.53      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.37/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.53  thf(t12_xboole_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.37/0.53  thf('13', plain,
% 0.37/0.53      (![X7 : $i, X8 : $i]:
% 0.37/0.53         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.37/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.53  thf('14', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.53  thf('15', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.53  thf('16', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.37/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.53  thf('17', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.37/0.53           = (X1))),
% 0.37/0.53      inference('demod', [status(thm)], ['11', '16'])).
% 0.37/0.53  thf('18', plain,
% 0.37/0.53      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B)) = (sk_C))),
% 0.37/0.53      inference('sup+', [status(thm)], ['5', '17'])).
% 0.37/0.53  thf('19', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.53  thf(t1_boole, axiom,
% 0.37/0.53    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.53  thf('20', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.37/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.53  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.53      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.53  thf('22', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (sk_C))),
% 0.37/0.53      inference('demod', [status(thm)], ['18', '21'])).
% 0.37/0.53  thf('23', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('24', plain,
% 0.37/0.53      (![X7 : $i, X8 : $i]:
% 0.37/0.53         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.37/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.53  thf('25', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.37/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.53  thf(t41_xboole_1, axiom,
% 0.37/0.53    (![A:$i,B:$i,C:$i]:
% 0.37/0.53     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.53       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.53  thf('26', plain,
% 0.37/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.37/0.53           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.37/0.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.37/0.53  thf('27', plain,
% 0.37/0.53      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.37/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.53  thf('28', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.53         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.37/0.53          (k4_xboole_0 @ X2 @ X1))),
% 0.37/0.53      inference('sup+', [status(thm)], ['26', '27'])).
% 0.37/0.53  thf('29', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_A))),
% 0.37/0.53      inference('sup+', [status(thm)], ['25', '28'])).
% 0.37/0.53  thf('30', plain, ((r1_tarski @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))),
% 0.37/0.53      inference('sup+', [status(thm)], ['22', '29'])).
% 0.37/0.53  thf('31', plain,
% 0.37/0.53      (![X7 : $i, X8 : $i]:
% 0.37/0.53         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.37/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.53  thf('32', plain,
% 0.37/0.53      (((k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))
% 0.37/0.53         = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.37/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.53  thf('33', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.37/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.53  thf('34', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.37/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.53  thf('35', plain,
% 0.37/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.37/0.53           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.37/0.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.37/0.53  thf('36', plain,
% 0.37/0.53      (![X13 : $i, X14 : $i]:
% 0.37/0.53         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.37/0.53           = (k2_xboole_0 @ X13 @ X14))),
% 0.37/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.53  thf('37', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.53         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.37/0.53           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.37/0.53      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.53  thf('38', plain,
% 0.37/0.53      (![X19 : $i, X20 : $i]:
% 0.37/0.53         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.37/0.53           = (k3_xboole_0 @ X19 @ X20))),
% 0.37/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.53  thf('39', plain,
% 0.37/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.37/0.53           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.37/0.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.37/0.53  thf('40', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.53         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.37/0.53           = (k4_xboole_0 @ X2 @ 
% 0.37/0.53              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.37/0.53      inference('sup+', [status(thm)], ['38', '39'])).
% 0.37/0.53  thf('41', plain,
% 0.37/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.37/0.53           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.37/0.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.37/0.53  thf('42', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.53         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.37/0.53           = (k4_xboole_0 @ X2 @ 
% 0.37/0.53              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.37/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.53  thf('43', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.37/0.53           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.37/0.53      inference('sup+', [status(thm)], ['37', '42'])).
% 0.37/0.53  thf('44', plain,
% 0.37/0.53      (![X13 : $i, X14 : $i]:
% 0.37/0.53         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.37/0.53           = (k2_xboole_0 @ X13 @ X14))),
% 0.37/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.53  thf('45', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.37/0.53           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.37/0.53      inference('demod', [status(thm)], ['43', '44'])).
% 0.37/0.53  thf(t3_boole, axiom,
% 0.37/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.53  thf('46', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.37/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.54  thf('47', plain,
% 0.37/0.54      (![X19 : $i, X20 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.37/0.54           = (k3_xboole_0 @ X19 @ X20))),
% 0.37/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.54  thf('48', plain,
% 0.37/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['46', '47'])).
% 0.37/0.54  thf(t2_boole, axiom,
% 0.37/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.54  thf('49', plain,
% 0.37/0.54      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.54  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.54      inference('demod', [status(thm)], ['48', '49'])).
% 0.37/0.54  thf('51', plain,
% 0.37/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.37/0.54           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.37/0.54  thf('52', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((k1_xboole_0)
% 0.37/0.54           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.37/0.54      inference('sup+', [status(thm)], ['50', '51'])).
% 0.37/0.54  thf('53', plain,
% 0.37/0.54      (![X13 : $i, X14 : $i]:
% 0.37/0.54         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.37/0.54           = (k2_xboole_0 @ X13 @ X14))),
% 0.37/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.54  thf('54', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.37/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.37/0.54  thf('55', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.37/0.54      inference('demod', [status(thm)], ['45', '54'])).
% 0.37/0.54  thf('56', plain,
% 0.37/0.54      (![X2 : $i, X4 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.54  thf('57', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.54          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.37/0.54  thf('58', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.37/0.54      inference('simplify', [status(thm)], ['57'])).
% 0.37/0.54  thf('59', plain,
% 0.37/0.54      (![X5 : $i, X6 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.37/0.54      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.54  thf('60', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.54  thf('61', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.37/0.54      inference('sup+', [status(thm)], ['34', '60'])).
% 0.37/0.54  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
