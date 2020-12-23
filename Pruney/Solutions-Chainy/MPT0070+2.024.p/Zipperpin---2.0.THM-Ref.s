%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.arB4Apfbb5

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:35 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 187 expanded)
%              Number of leaves         :   19 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  604 (1381 expanded)
%              Number of equality atoms :   66 ( 148 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
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
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('23',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_C ) @ sk_C )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_C ) @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('26',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('44',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25','40','41','42','43'])).

thf('45',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('49',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('51',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['44','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.arB4Apfbb5
% 0.16/0.37  % Computer   : n020.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 10:07:22 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.53/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.70  % Solved by: fo/fo7.sh
% 0.53/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.70  % done 649 iterations in 0.214s
% 0.53/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.70  % SZS output start Refutation
% 0.53/0.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.53/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.70  thf(t63_xboole_1, conjecture,
% 0.53/0.70    (![A:$i,B:$i,C:$i]:
% 0.53/0.70     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.53/0.70       ( r1_xboole_0 @ A @ C ) ))).
% 0.53/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.70        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.53/0.70          ( r1_xboole_0 @ A @ C ) ) )),
% 0.53/0.70    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.53/0.70  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('1', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf(d7_xboole_0, axiom,
% 0.53/0.70    (![A:$i,B:$i]:
% 0.53/0.70     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.53/0.70       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.53/0.70  thf('2', plain,
% 0.53/0.70      (![X2 : $i, X3 : $i]:
% 0.53/0.70         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.53/0.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.53/0.70  thf('3', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.53/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.70  thf(commutativity_k3_xboole_0, axiom,
% 0.53/0.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.53/0.70  thf('4', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.70  thf(t48_xboole_1, axiom,
% 0.53/0.70    (![A:$i,B:$i]:
% 0.53/0.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.70  thf('5', plain,
% 0.53/0.70      (![X17 : $i, X18 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.53/0.70           = (k3_xboole_0 @ X17 @ X18))),
% 0.53/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.70  thf(t39_xboole_1, axiom,
% 0.53/0.70    (![A:$i,B:$i]:
% 0.53/0.70     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.53/0.70  thf('6', plain,
% 0.53/0.70      (![X11 : $i, X12 : $i]:
% 0.53/0.70         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.53/0.70           = (k2_xboole_0 @ X11 @ X12))),
% 0.53/0.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.53/0.70  thf('7', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]:
% 0.53/0.70         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.70           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.53/0.70      inference('sup+', [status(thm)], ['5', '6'])).
% 0.53/0.70  thf('8', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]:
% 0.53/0.70         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.70           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.53/0.70      inference('sup+', [status(thm)], ['4', '7'])).
% 0.53/0.70  thf('9', plain,
% 0.53/0.70      (((k2_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ k1_xboole_0)
% 0.53/0.70         = (k2_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_C))),
% 0.53/0.70      inference('sup+', [status(thm)], ['3', '8'])).
% 0.53/0.70  thf(t1_boole, axiom,
% 0.53/0.70    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.53/0.70  thf('10', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.53/0.70      inference('cnf', [status(esa)], [t1_boole])).
% 0.53/0.70  thf('11', plain,
% 0.53/0.70      (((k4_xboole_0 @ sk_C @ sk_B)
% 0.53/0.70         = (k2_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_C))),
% 0.53/0.70      inference('demod', [status(thm)], ['9', '10'])).
% 0.53/0.70  thf(t36_xboole_1, axiom,
% 0.53/0.70    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.70  thf('12', plain,
% 0.53/0.70      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.53/0.70      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.53/0.70  thf(l32_xboole_1, axiom,
% 0.53/0.70    (![A:$i,B:$i]:
% 0.53/0.70     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.70  thf('13', plain,
% 0.53/0.70      (![X5 : $i, X7 : $i]:
% 0.53/0.70         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.53/0.70      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.53/0.70  thf('14', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.53/0.70      inference('sup-', [status(thm)], ['12', '13'])).
% 0.53/0.70  thf(t41_xboole_1, axiom,
% 0.53/0.70    (![A:$i,B:$i,C:$i]:
% 0.53/0.70     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.53/0.70       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.53/0.70  thf('15', plain,
% 0.53/0.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.53/0.70           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.53/0.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.70  thf('16', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.53/0.70      inference('demod', [status(thm)], ['14', '15'])).
% 0.53/0.70  thf('17', plain,
% 0.53/0.70      (![X17 : $i, X18 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.53/0.70           = (k3_xboole_0 @ X17 @ X18))),
% 0.53/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.70  thf('18', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.53/0.70           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.53/0.70      inference('sup+', [status(thm)], ['16', '17'])).
% 0.53/0.70  thf(t3_boole, axiom,
% 0.53/0.70    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.53/0.70  thf('19', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.53/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.53/0.70  thf('20', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]:
% 0.53/0.70         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.53/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.53/0.70  thf('21', plain,
% 0.53/0.70      (((sk_C) = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 0.53/0.70      inference('sup+', [status(thm)], ['11', '20'])).
% 0.53/0.70  thf('22', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]:
% 0.53/0.70         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.70           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.53/0.70      inference('sup+', [status(thm)], ['4', '7'])).
% 0.53/0.70  thf('23', plain,
% 0.53/0.70      (((k2_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_C) @ 
% 0.53/0.70         sk_C)
% 0.53/0.70         = (k2_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_C) @ 
% 0.53/0.70            (k4_xboole_0 @ sk_C @ sk_B)))),
% 0.53/0.70      inference('sup+', [status(thm)], ['21', '22'])).
% 0.53/0.70  thf('24', plain,
% 0.53/0.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.53/0.70           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.53/0.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.70  thf('25', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.53/0.70      inference('demod', [status(thm)], ['14', '15'])).
% 0.53/0.70  thf('26', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.53/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.53/0.70  thf('27', plain,
% 0.53/0.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.53/0.70           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.53/0.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.70  thf('28', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ X0 @ X1)
% 0.53/0.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.53/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.53/0.70  thf('29', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.53/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.53/0.70  thf('30', plain,
% 0.53/0.70      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.53/0.70      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.53/0.70  thf('31', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.53/0.70      inference('sup+', [status(thm)], ['29', '30'])).
% 0.53/0.70  thf('32', plain,
% 0.53/0.70      (![X5 : $i, X7 : $i]:
% 0.53/0.70         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.53/0.70      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.53/0.70  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.70      inference('sup-', [status(thm)], ['31', '32'])).
% 0.53/0.70  thf('34', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 0.53/0.70      inference('sup+', [status(thm)], ['28', '33'])).
% 0.53/0.70  thf('35', plain,
% 0.53/0.70      (![X17 : $i, X18 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.53/0.70           = (k3_xboole_0 @ X17 @ X18))),
% 0.53/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.70  thf('36', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.53/0.70           = (k3_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0))),
% 0.53/0.70      inference('sup+', [status(thm)], ['34', '35'])).
% 0.53/0.70  thf('37', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.53/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.53/0.70  thf('38', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.70  thf('39', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]:
% 0.53/0.70         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.53/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.53/0.70  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.53/0.70      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.53/0.70  thf('41', plain,
% 0.53/0.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.53/0.70           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.53/0.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.70  thf('42', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.53/0.70      inference('demod', [status(thm)], ['14', '15'])).
% 0.53/0.70  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.53/0.70      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.53/0.70  thf('44', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.53/0.70      inference('demod', [status(thm)],
% 0.53/0.70                ['23', '24', '25', '40', '41', '42', '43'])).
% 0.53/0.70  thf('45', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('46', plain,
% 0.53/0.70      (![X5 : $i, X7 : $i]:
% 0.53/0.70         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.53/0.70      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.53/0.70  thf('47', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.53/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.53/0.70  thf('48', plain,
% 0.53/0.70      (![X11 : $i, X12 : $i]:
% 0.53/0.70         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.53/0.70           = (k2_xboole_0 @ X11 @ X12))),
% 0.53/0.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.53/0.70  thf('49', plain,
% 0.53/0.70      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.53/0.70      inference('sup+', [status(thm)], ['47', '48'])).
% 0.53/0.70  thf('50', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.53/0.70      inference('cnf', [status(esa)], [t1_boole])).
% 0.53/0.70  thf('51', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.53/0.70      inference('demod', [status(thm)], ['49', '50'])).
% 0.53/0.70  thf('52', plain,
% 0.53/0.70      (![X17 : $i, X18 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.53/0.70           = (k3_xboole_0 @ X17 @ X18))),
% 0.53/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.70  thf('53', plain,
% 0.53/0.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.53/0.70           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.53/0.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.70  thf('54', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.70         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.53/0.70           = (k4_xboole_0 @ X2 @ 
% 0.53/0.70              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.53/0.70      inference('sup+', [status(thm)], ['52', '53'])).
% 0.53/0.70  thf('55', plain,
% 0.53/0.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.53/0.70           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.53/0.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.70  thf('56', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.70         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.53/0.70           = (k4_xboole_0 @ X2 @ 
% 0.53/0.70              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.53/0.70      inference('demod', [status(thm)], ['54', '55'])).
% 0.53/0.70  thf('57', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.53/0.70           = (k4_xboole_0 @ X0 @ 
% 0.53/0.70              (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_B))))),
% 0.53/0.70      inference('sup+', [status(thm)], ['51', '56'])).
% 0.53/0.70  thf('58', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.70  thf('59', plain,
% 0.53/0.70      (![X11 : $i, X12 : $i]:
% 0.53/0.70         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.53/0.70           = (k2_xboole_0 @ X11 @ X12))),
% 0.53/0.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.53/0.70  thf('60', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]:
% 0.53/0.70         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.53/0.70      inference('demod', [status(thm)], ['14', '15'])).
% 0.53/0.70  thf('61', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 0.53/0.70      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.53/0.70  thf('62', plain,
% 0.53/0.70      (![X2 : $i, X4 : $i]:
% 0.53/0.70         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.53/0.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.53/0.70  thf('63', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         (((k1_xboole_0) != (k1_xboole_0))
% 0.53/0.70          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.53/0.70  thf('64', plain,
% 0.53/0.70      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.53/0.70      inference('simplify', [status(thm)], ['63'])).
% 0.53/0.70  thf('65', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.53/0.70      inference('sup+', [status(thm)], ['44', '64'])).
% 0.53/0.70  thf('66', plain, ($false), inference('demod', [status(thm)], ['0', '65'])).
% 0.53/0.70  
% 0.53/0.70  % SZS output end Refutation
% 0.53/0.70  
% 0.53/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
