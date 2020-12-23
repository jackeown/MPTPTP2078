%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BaglnA75lh

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:04 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 488 expanded)
%              Number of leaves         :   21 ( 172 expanded)
%              Depth                    :   21
%              Number of atoms          :  825 (3396 expanded)
%              Number of equality atoms :   93 ( 407 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X21: $i] :
      ( r1_xboole_0 @ X21 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_B ) @ sk_C )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ sk_B ) @ sk_C )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('25',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['16','23','24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('61',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('63',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('64',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('65',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','70'])).

thf('72',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('75',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C ) ),
    inference('sup+',[status(thm)],['73','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C ) ),
    inference('sup+',[status(thm)],['50','83'])).

thf('85',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','88'])).

thf('90',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('91',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('93',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('94',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('96',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['0','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BaglnA75lh
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:52:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.99/1.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.19  % Solved by: fo/fo7.sh
% 0.99/1.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.19  % done 1373 iterations in 0.737s
% 0.99/1.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.19  % SZS output start Refutation
% 0.99/1.19  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.99/1.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.19  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.19  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.19  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.99/1.19  thf(sk_C_type, type, sk_C: $i).
% 0.99/1.19  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.19  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.99/1.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.19  thf(t73_xboole_1, conjecture,
% 0.99/1.19    (![A:$i,B:$i,C:$i]:
% 0.99/1.19     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.99/1.19       ( r1_tarski @ A @ B ) ))).
% 0.99/1.19  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.19    (~( ![A:$i,B:$i,C:$i]:
% 0.99/1.19        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.99/1.19            ( r1_xboole_0 @ A @ C ) ) =>
% 0.99/1.19          ( r1_tarski @ A @ B ) ) )),
% 0.99/1.19    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.99/1.19  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(t3_boole, axiom,
% 0.99/1.19    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.99/1.19  thf('1', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.99/1.19      inference('cnf', [status(esa)], [t3_boole])).
% 0.99/1.19  thf(t48_xboole_1, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.99/1.19  thf('2', plain,
% 0.99/1.19      (![X16 : $i, X17 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.99/1.19           = (k3_xboole_0 @ X16 @ X17))),
% 0.99/1.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.19  thf('3', plain,
% 0.99/1.19      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.99/1.19      inference('sup+', [status(thm)], ['1', '2'])).
% 0.99/1.19  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.99/1.19  thf('4', plain, (![X21 : $i]: (r1_xboole_0 @ X21 @ k1_xboole_0)),
% 0.99/1.19      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.99/1.19  thf(d7_xboole_0, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.99/1.19       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.99/1.19  thf('5', plain,
% 0.99/1.19      (![X4 : $i, X5 : $i]:
% 0.99/1.19         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.99/1.19      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.99/1.19  thf('6', plain,
% 0.99/1.19      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.99/1.19      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.19  thf('7', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['3', '6'])).
% 0.99/1.19  thf('8', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(t12_xboole_1, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.99/1.19  thf('9', plain,
% 0.99/1.19      (![X8 : $i, X9 : $i]:
% 0.99/1.19         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.99/1.19      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.99/1.19  thf('10', plain,
% 0.99/1.19      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.99/1.19         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.99/1.19      inference('sup-', [status(thm)], ['8', '9'])).
% 0.99/1.19  thf(t41_xboole_1, axiom,
% 0.99/1.19    (![A:$i,B:$i,C:$i]:
% 0.99/1.19     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.99/1.19       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.99/1.19  thf('11', plain,
% 0.99/1.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.99/1.19           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.99/1.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.19  thf('12', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ 
% 0.99/1.19           (k2_xboole_0 @ sk_B @ sk_C))
% 0.99/1.19           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.99/1.19      inference('sup+', [status(thm)], ['10', '11'])).
% 0.99/1.19  thf('13', plain,
% 0.99/1.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.99/1.19           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.99/1.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.19  thf('14', plain,
% 0.99/1.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.99/1.19           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.99/1.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.19  thf('15', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ sk_B) @ 
% 0.99/1.19           sk_C) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C))),
% 0.99/1.19      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.99/1.19  thf('16', plain,
% 0.99/1.19      (((k4_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ sk_B) @ sk_C)
% 0.99/1.19         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.99/1.19      inference('sup+', [status(thm)], ['7', '15'])).
% 0.99/1.19  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['3', '6'])).
% 0.99/1.19  thf(idempotence_k2_xboole_0, axiom,
% 0.99/1.19    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.99/1.19  thf('18', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 0.99/1.19      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.99/1.19  thf('19', plain,
% 0.99/1.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.99/1.19           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.99/1.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.19  thf('20', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.99/1.19           = (k4_xboole_0 @ X1 @ X0))),
% 0.99/1.19      inference('sup+', [status(thm)], ['18', '19'])).
% 0.99/1.19  thf('21', plain,
% 0.99/1.19      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.99/1.19      inference('sup+', [status(thm)], ['17', '20'])).
% 0.99/1.19  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['3', '6'])).
% 0.99/1.19  thf('23', plain,
% 0.99/1.19      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['21', '22'])).
% 0.99/1.19  thf('24', plain,
% 0.99/1.19      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['21', '22'])).
% 0.99/1.19  thf('25', plain,
% 0.99/1.19      (((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.99/1.19      inference('demod', [status(thm)], ['16', '23', '24'])).
% 0.99/1.19  thf('26', plain,
% 0.99/1.19      (![X16 : $i, X17 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.99/1.19           = (k3_xboole_0 @ X16 @ X17))),
% 0.99/1.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.19  thf('27', plain,
% 0.99/1.19      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.99/1.19         = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.99/1.19      inference('sup+', [status(thm)], ['25', '26'])).
% 0.99/1.19  thf('28', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.99/1.19      inference('cnf', [status(esa)], [t3_boole])).
% 0.99/1.19  thf(commutativity_k3_xboole_0, axiom,
% 0.99/1.19    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.99/1.19  thf('29', plain,
% 0.99/1.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.99/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.19  thf('30', plain,
% 0.99/1.19      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.99/1.19         = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.99/1.19  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['3', '6'])).
% 0.99/1.19  thf(commutativity_k2_xboole_0, axiom,
% 0.99/1.19    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.99/1.19  thf('32', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.19  thf(t7_xboole_1, axiom,
% 0.99/1.19    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.99/1.19  thf('33', plain,
% 0.99/1.19      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.99/1.19      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.99/1.19  thf('34', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.99/1.19      inference('sup+', [status(thm)], ['32', '33'])).
% 0.99/1.19  thf('35', plain,
% 0.99/1.19      (![X8 : $i, X9 : $i]:
% 0.99/1.19         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.99/1.19      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.99/1.19  thf('36', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.99/1.19           = (k2_xboole_0 @ X1 @ X0))),
% 0.99/1.19      inference('sup-', [status(thm)], ['34', '35'])).
% 0.99/1.19  thf('37', plain,
% 0.99/1.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.99/1.19           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.99/1.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.19  thf('38', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.99/1.19           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.99/1.19      inference('sup+', [status(thm)], ['36', '37'])).
% 0.99/1.19  thf('39', plain,
% 0.99/1.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.99/1.19           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.99/1.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.19  thf('40', plain,
% 0.99/1.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.99/1.19           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.99/1.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.19  thf('41', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ X0)
% 0.99/1.19           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.99/1.19      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.99/1.19  thf('42', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X1) @ X0)
% 0.99/1.19           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.99/1.19      inference('sup+', [status(thm)], ['31', '41'])).
% 0.99/1.19  thf('43', plain,
% 0.99/1.19      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['21', '22'])).
% 0.99/1.19  thf('44', plain,
% 0.99/1.19      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['21', '22'])).
% 0.99/1.19  thf('45', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.99/1.19      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.99/1.19  thf('46', plain,
% 0.99/1.19      (![X16 : $i, X17 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.99/1.19           = (k3_xboole_0 @ X16 @ X17))),
% 0.99/1.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.19  thf('47', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.99/1.19           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.99/1.19      inference('sup+', [status(thm)], ['45', '46'])).
% 0.99/1.19  thf('48', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.99/1.19      inference('cnf', [status(esa)], [t3_boole])).
% 0.99/1.19  thf('49', plain,
% 0.99/1.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.99/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.19  thf('50', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ X0 @ X1)
% 0.99/1.19           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.99/1.19      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.99/1.19  thf('51', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('52', plain,
% 0.99/1.19      (![X4 : $i, X5 : $i]:
% 0.99/1.19         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.99/1.19      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.99/1.19  thf('53', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.99/1.19      inference('sup-', [status(thm)], ['51', '52'])).
% 0.99/1.19  thf('54', plain,
% 0.99/1.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.99/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.19  thf('55', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['53', '54'])).
% 0.99/1.19  thf('56', plain,
% 0.99/1.19      (![X16 : $i, X17 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.99/1.19           = (k3_xboole_0 @ X16 @ X17))),
% 0.99/1.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.19  thf('57', plain,
% 0.99/1.19      (![X16 : $i, X17 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.99/1.19           = (k3_xboole_0 @ X16 @ X17))),
% 0.99/1.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.19  thf('58', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.99/1.19           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.99/1.19      inference('sup+', [status(thm)], ['56', '57'])).
% 0.99/1.19  thf('59', plain,
% 0.99/1.19      (((k4_xboole_0 @ sk_C @ k1_xboole_0)
% 0.99/1.19         = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.99/1.19      inference('sup+', [status(thm)], ['55', '58'])).
% 0.99/1.19  thf('60', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.99/1.19      inference('cnf', [status(esa)], [t3_boole])).
% 0.99/1.19  thf('61', plain,
% 0.99/1.19      (((sk_C) = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['59', '60'])).
% 0.99/1.19  thf('62', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ X0 @ X1)
% 0.99/1.19           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.99/1.19      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.99/1.19  thf('63', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.99/1.19      inference('demod', [status(thm)], ['61', '62'])).
% 0.99/1.19  thf(t17_xboole_1, axiom,
% 0.99/1.19    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.99/1.19  thf('64', plain,
% 0.99/1.19      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.99/1.19      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.99/1.19  thf('65', plain,
% 0.99/1.19      (![X8 : $i, X9 : $i]:
% 0.99/1.19         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.99/1.19      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.99/1.19  thf('66', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.99/1.19      inference('sup-', [status(thm)], ['64', '65'])).
% 0.99/1.19  thf('67', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.19  thf('68', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 0.99/1.19      inference('demod', [status(thm)], ['66', '67'])).
% 0.99/1.19  thf('69', plain,
% 0.99/1.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.99/1.19           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.99/1.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.99/1.19  thf('70', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 0.99/1.19           = (k4_xboole_0 @ X2 @ X0))),
% 0.99/1.19      inference('sup+', [status(thm)], ['68', '69'])).
% 0.99/1.19  thf('71', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0))
% 0.99/1.19           = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.99/1.19      inference('sup+', [status(thm)], ['63', '70'])).
% 0.99/1.19  thf('72', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.99/1.19      inference('demod', [status(thm)], ['61', '62'])).
% 0.99/1.19  thf('73', plain,
% 0.99/1.19      (![X0 : $i]: ((k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)) = (sk_C))),
% 0.99/1.19      inference('demod', [status(thm)], ['71', '72'])).
% 0.99/1.19  thf('74', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.99/1.19           = (k4_xboole_0 @ X1 @ X0))),
% 0.99/1.19      inference('sup+', [status(thm)], ['18', '19'])).
% 0.99/1.19  thf('75', plain,
% 0.99/1.19      (![X16 : $i, X17 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.99/1.19           = (k3_xboole_0 @ X16 @ X17))),
% 0.99/1.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.19  thf('76', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.99/1.19           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.99/1.19      inference('sup+', [status(thm)], ['74', '75'])).
% 0.99/1.19  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['3', '6'])).
% 0.99/1.19  thf('78', plain,
% 0.99/1.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.99/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.19  thf('79', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.99/1.19      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.99/1.19  thf('80', plain,
% 0.99/1.19      (![X4 : $i, X6 : $i]:
% 0.99/1.19         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.99/1.19      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.99/1.19  thf('81', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         (((k1_xboole_0) != (k1_xboole_0))
% 0.99/1.19          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.99/1.19      inference('sup-', [status(thm)], ['79', '80'])).
% 0.99/1.19  thf('82', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.99/1.19      inference('simplify', [status(thm)], ['81'])).
% 0.99/1.19  thf('83', plain,
% 0.99/1.19      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_C)),
% 0.99/1.19      inference('sup+', [status(thm)], ['73', '82'])).
% 0.99/1.19  thf('84', plain,
% 0.99/1.19      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_C)),
% 0.99/1.19      inference('sup+', [status(thm)], ['50', '83'])).
% 0.99/1.19  thf('85', plain,
% 0.99/1.19      (![X4 : $i, X5 : $i]:
% 0.99/1.19         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.99/1.19      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.99/1.19  thf('86', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         ((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_C) = (k1_xboole_0))),
% 0.99/1.19      inference('sup-', [status(thm)], ['84', '85'])).
% 0.99/1.19  thf('87', plain,
% 0.99/1.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.99/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.19  thf('88', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         ((k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['86', '87'])).
% 0.99/1.19  thf('89', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['30', '88'])).
% 0.99/1.19  thf('90', plain,
% 0.99/1.19      (![X16 : $i, X17 : $i]:
% 0.99/1.19         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.99/1.19           = (k3_xboole_0 @ X16 @ X17))),
% 0.99/1.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.19  thf('91', plain,
% 0.99/1.19      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.99/1.19      inference('sup+', [status(thm)], ['89', '90'])).
% 0.99/1.19  thf('92', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.99/1.19      inference('cnf', [status(esa)], [t3_boole])).
% 0.99/1.19  thf('93', plain,
% 0.99/1.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.99/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.19  thf('94', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.99/1.19      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.99/1.19  thf('95', plain,
% 0.99/1.19      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.99/1.19      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.99/1.19  thf('96', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.99/1.19      inference('sup+', [status(thm)], ['94', '95'])).
% 0.99/1.19  thf('97', plain, ($false), inference('demod', [status(thm)], ['0', '96'])).
% 0.99/1.19  
% 0.99/1.19  % SZS output end Refutation
% 0.99/1.19  
% 1.06/1.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
