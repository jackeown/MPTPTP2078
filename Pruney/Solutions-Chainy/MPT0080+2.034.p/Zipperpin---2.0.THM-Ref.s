%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BPiAcuMgcF

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:08 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 316 expanded)
%              Number of leaves         :   24 ( 116 expanded)
%              Depth                    :   21
%              Number of atoms          :  883 (2385 expanded)
%              Number of equality atoms :   87 ( 259 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_C_2
    = ( k2_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ sk_A ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('37',plain,(
    ! [X26: $i] :
      ( r1_xboole_0 @ X26 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('49',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = sk_A ),
    inference(demod,[status(thm)],['32','33','44','45','46','47','48','49'])).

thf('51',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['14','52'])).

thf('54',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = sk_A ),
    inference(demod,[status(thm)],['32','33','44','45','46','47','48','49'])).

thf('56',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('62',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('68',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('78',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('82',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('86',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['1','89'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('91',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X28 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('92',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X13 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('94',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BPiAcuMgcF
% 0.14/0.36  % Computer   : n013.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:18:10 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.67/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.90  % Solved by: fo/fo7.sh
% 0.67/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.90  % done 1418 iterations in 0.438s
% 0.67/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.90  % SZS output start Refutation
% 0.67/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.90  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.67/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.67/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.90  thf(t73_xboole_1, conjecture,
% 0.67/0.90    (![A:$i,B:$i,C:$i]:
% 0.67/0.90     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.67/0.90       ( r1_tarski @ A @ B ) ))).
% 0.67/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.90    (~( ![A:$i,B:$i,C:$i]:
% 0.67/0.90        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.67/0.90            ( r1_xboole_0 @ A @ C ) ) =>
% 0.67/0.90          ( r1_tarski @ A @ B ) ) )),
% 0.67/0.90    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.67/0.90  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf(t3_xboole_0, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.67/0.90            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.67/0.90       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.67/0.90            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.67/0.90  thf('1', plain,
% 0.67/0.90      (![X5 : $i, X6 : $i]:
% 0.67/0.90         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.67/0.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.67/0.90  thf('2', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf(l32_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.90  thf('3', plain,
% 0.67/0.90      (![X13 : $i, X15 : $i]:
% 0.67/0.90         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 0.67/0.90          | ~ (r1_tarski @ X13 @ X15))),
% 0.67/0.90      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.67/0.90  thf('4', plain,
% 0.67/0.90      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)) = (k1_xboole_0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['2', '3'])).
% 0.67/0.90  thf(t41_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i,C:$i]:
% 0.67/0.90     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.67/0.90       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.67/0.90  thf('5', plain,
% 0.67/0.90      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 0.67/0.90           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.67/0.90  thf(t39_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.67/0.90  thf('6', plain,
% 0.67/0.90      (![X16 : $i, X17 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 0.67/0.90           = (k2_xboole_0 @ X16 @ X17))),
% 0.67/0.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.67/0.90  thf('7', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.67/0.90           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['5', '6'])).
% 0.67/0.90  thf('8', plain,
% 0.67/0.90      (((k2_xboole_0 @ sk_C_2 @ k1_xboole_0)
% 0.67/0.90         = (k2_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['4', '7'])).
% 0.67/0.90  thf(t40_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.67/0.90  thf('9', plain,
% 0.67/0.90      (![X19 : $i, X20 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20)
% 0.67/0.90           = (k4_xboole_0 @ X19 @ X20))),
% 0.67/0.90      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.67/0.90  thf(t3_boole, axiom,
% 0.67/0.90    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.67/0.90  thf('10', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.67/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.67/0.90  thf('11', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.67/0.90      inference('sup+', [status(thm)], ['9', '10'])).
% 0.67/0.90  thf('12', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.67/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.67/0.90  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.67/0.90      inference('sup+', [status(thm)], ['11', '12'])).
% 0.67/0.90  thf('14', plain,
% 0.67/0.90      (((sk_C_2) = (k2_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.67/0.90      inference('demod', [status(thm)], ['8', '13'])).
% 0.67/0.90  thf('15', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf(d7_xboole_0, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.67/0.90       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.67/0.90  thf('16', plain,
% 0.67/0.90      (![X2 : $i, X3 : $i]:
% 0.67/0.90         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.67/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.67/0.90  thf('17', plain, (((k3_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['15', '16'])).
% 0.67/0.90  thf(t48_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.67/0.90  thf('18', plain,
% 0.67/0.90      (![X24 : $i, X25 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.67/0.90           = (k3_xboole_0 @ X24 @ X25))),
% 0.67/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.67/0.90  thf('19', plain,
% 0.67/0.90      (![X16 : $i, X17 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 0.67/0.90           = (k2_xboole_0 @ X16 @ X17))),
% 0.67/0.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.67/0.90  thf('20', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.67/0.90           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.67/0.90      inference('sup+', [status(thm)], ['18', '19'])).
% 0.67/0.90  thf(commutativity_k2_xboole_0, axiom,
% 0.67/0.90    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.67/0.90  thf('21', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.67/0.90  thf('22', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.67/0.90  thf('23', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.67/0.90           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.90      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.67/0.90  thf('24', plain,
% 0.67/0.90      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_2))
% 0.67/0.90         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_2)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['17', '23'])).
% 0.67/0.90  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.67/0.90      inference('sup+', [status(thm)], ['11', '12'])).
% 0.67/0.90  thf('26', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.67/0.90  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.67/0.90      inference('sup+', [status(thm)], ['25', '26'])).
% 0.67/0.90  thf('28', plain,
% 0.67/0.90      (((k4_xboole_0 @ sk_A @ sk_C_2)
% 0.67/0.90         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_2)))),
% 0.67/0.90      inference('demod', [status(thm)], ['24', '27'])).
% 0.67/0.90  thf('29', plain,
% 0.67/0.90      (![X16 : $i, X17 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 0.67/0.90           = (k2_xboole_0 @ X16 @ X17))),
% 0.67/0.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.67/0.90  thf('30', plain,
% 0.67/0.90      (![X19 : $i, X20 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20)
% 0.67/0.90           = (k4_xboole_0 @ X19 @ X20))),
% 0.67/0.90      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.67/0.90  thf('31', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.67/0.90           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['29', '30'])).
% 0.67/0.90  thf('32', plain,
% 0.67/0.90      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_2) @ 
% 0.67/0.90         (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_2) @ sk_A))
% 0.67/0.90         = (k4_xboole_0 @ sk_A @ 
% 0.67/0.90            (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_2) @ sk_A)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['28', '31'])).
% 0.67/0.90  thf('33', plain,
% 0.67/0.90      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 0.67/0.90           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.67/0.90  thf('34', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.67/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.67/0.90  thf('35', plain,
% 0.67/0.90      (![X24 : $i, X25 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.67/0.90           = (k3_xboole_0 @ X24 @ X25))),
% 0.67/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.67/0.90  thf('36', plain,
% 0.67/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.67/0.90      inference('sup+', [status(thm)], ['34', '35'])).
% 0.67/0.90  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.67/0.90  thf('37', plain, (![X26 : $i]: (r1_xboole_0 @ X26 @ k1_xboole_0)),
% 0.67/0.90      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.67/0.90  thf('38', plain,
% 0.67/0.90      (![X2 : $i, X3 : $i]:
% 0.67/0.90         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.67/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.67/0.90  thf('39', plain,
% 0.67/0.90      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['37', '38'])).
% 0.67/0.90  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.67/0.90      inference('demod', [status(thm)], ['36', '39'])).
% 0.67/0.90  thf('41', plain,
% 0.67/0.90      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 0.67/0.90           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.67/0.90  thf('42', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k1_xboole_0)
% 0.67/0.90           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.67/0.90      inference('sup+', [status(thm)], ['40', '41'])).
% 0.67/0.90  thf('43', plain,
% 0.67/0.90      (![X16 : $i, X17 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 0.67/0.90           = (k2_xboole_0 @ X16 @ X17))),
% 0.67/0.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.67/0.90  thf('44', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.67/0.90      inference('demod', [status(thm)], ['42', '43'])).
% 0.67/0.90  thf('45', plain,
% 0.67/0.90      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 0.67/0.90           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.67/0.90  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.67/0.90      inference('sup+', [status(thm)], ['11', '12'])).
% 0.67/0.90  thf('47', plain,
% 0.67/0.90      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 0.67/0.90           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.67/0.90  thf('48', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.67/0.90      inference('demod', [status(thm)], ['42', '43'])).
% 0.67/0.90  thf('49', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.67/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.67/0.90  thf('50', plain, (((k4_xboole_0 @ sk_A @ sk_C_2) = (sk_A))),
% 0.67/0.90      inference('demod', [status(thm)],
% 0.67/0.90                ['32', '33', '44', '45', '46', '47', '48', '49'])).
% 0.67/0.90  thf('51', plain,
% 0.67/0.90      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 0.67/0.90           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.67/0.90  thf('52', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ sk_A @ X0)
% 0.67/0.90           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_2 @ X0)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['50', '51'])).
% 0.67/0.90  thf('53', plain,
% 0.67/0.90      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.67/0.90         = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 0.67/0.90      inference('sup+', [status(thm)], ['14', '52'])).
% 0.67/0.90  thf('54', plain,
% 0.67/0.90      (![X24 : $i, X25 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.67/0.90           = (k3_xboole_0 @ X24 @ X25))),
% 0.67/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.67/0.90  thf('55', plain, (((k4_xboole_0 @ sk_A @ sk_C_2) = (sk_A))),
% 0.67/0.90      inference('demod', [status(thm)],
% 0.67/0.90                ['32', '33', '44', '45', '46', '47', '48', '49'])).
% 0.67/0.90  thf('56', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.67/0.90      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.67/0.90  thf('57', plain,
% 0.67/0.90      (![X24 : $i, X25 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.67/0.90           = (k3_xboole_0 @ X24 @ X25))),
% 0.67/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.67/0.90  thf('58', plain,
% 0.67/0.90      (![X24 : $i, X25 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.67/0.90           = (k3_xboole_0 @ X24 @ X25))),
% 0.67/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.67/0.90  thf('59', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.67/0.90           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['57', '58'])).
% 0.67/0.90  thf('60', plain,
% 0.67/0.90      (((k4_xboole_0 @ sk_A @ sk_A)
% 0.67/0.90         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['56', '59'])).
% 0.67/0.90  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.67/0.90      inference('demod', [status(thm)], ['36', '39'])).
% 0.67/0.90  thf('62', plain,
% 0.67/0.90      (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.67/0.90      inference('demod', [status(thm)], ['60', '61'])).
% 0.67/0.90  thf('63', plain,
% 0.67/0.90      (![X2 : $i, X4 : $i]:
% 0.67/0.90         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.67/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.67/0.90  thf('64', plain,
% 0.67/0.90      ((((k1_xboole_0) != (k1_xboole_0))
% 0.67/0.90        | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['62', '63'])).
% 0.67/0.90  thf('65', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.67/0.90      inference('simplify', [status(thm)], ['64'])).
% 0.67/0.90  thf('66', plain,
% 0.67/0.90      (![X5 : $i, X6 : $i]:
% 0.67/0.90         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.67/0.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.67/0.90  thf('67', plain,
% 0.67/0.90      (![X5 : $i, X6 : $i]:
% 0.67/0.90         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X6))),
% 0.67/0.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.67/0.90  thf('68', plain,
% 0.67/0.90      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.67/0.90         (~ (r2_hidden @ X7 @ X5)
% 0.67/0.90          | ~ (r2_hidden @ X7 @ X8)
% 0.67/0.90          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.67/0.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.67/0.90  thf('69', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.90         ((r1_xboole_0 @ X1 @ X0)
% 0.67/0.90          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.67/0.90          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.67/0.90      inference('sup-', [status(thm)], ['67', '68'])).
% 0.67/0.90  thf('70', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((r1_xboole_0 @ X0 @ X1)
% 0.67/0.90          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.67/0.90          | (r1_xboole_0 @ X0 @ X1))),
% 0.67/0.90      inference('sup-', [status(thm)], ['66', '69'])).
% 0.67/0.90  thf('71', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.67/0.90      inference('simplify', [status(thm)], ['70'])).
% 0.67/0.90  thf('72', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)),
% 0.67/0.90      inference('sup-', [status(thm)], ['65', '71'])).
% 0.67/0.90  thf('73', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.67/0.90      inference('demod', [status(thm)], ['36', '39'])).
% 0.67/0.90  thf('74', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.67/0.90           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['5', '6'])).
% 0.67/0.90  thf('75', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.67/0.90           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['73', '74'])).
% 0.67/0.90  thf('76', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.67/0.90      inference('sup+', [status(thm)], ['11', '12'])).
% 0.67/0.90  thf('77', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.67/0.90  thf('78', plain,
% 0.67/0.90      (![X19 : $i, X20 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20)
% 0.67/0.90           = (k4_xboole_0 @ X19 @ X20))),
% 0.67/0.90      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.67/0.90  thf('79', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.67/0.90           = (k4_xboole_0 @ X0 @ X1))),
% 0.67/0.90      inference('sup+', [status(thm)], ['77', '78'])).
% 0.67/0.90  thf('80', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.90      inference('demod', [status(thm)], ['75', '76', '79'])).
% 0.67/0.90  thf('81', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.67/0.90      inference('demod', [status(thm)], ['42', '43'])).
% 0.67/0.90  thf('82', plain,
% 0.67/0.90      (![X24 : $i, X25 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.67/0.90           = (k3_xboole_0 @ X24 @ X25))),
% 0.67/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.67/0.90  thf('83', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.67/0.90           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['81', '82'])).
% 0.67/0.90  thf('84', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.67/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.67/0.90  thf('85', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.67/0.90      inference('demod', [status(thm)], ['83', '84'])).
% 0.67/0.90  thf(t4_xboole_0, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.67/0.90            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.67/0.90       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.67/0.90            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.67/0.90  thf('86', plain,
% 0.67/0.90      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.67/0.90         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.67/0.90          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.67/0.90      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.67/0.90  thf('87', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.90         (~ (r2_hidden @ X2 @ X0)
% 0.67/0.90          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['85', '86'])).
% 0.67/0.90  thf('88', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.90         (~ (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.67/0.90          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['80', '87'])).
% 0.67/0.90  thf('89', plain,
% 0.67/0.90      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.67/0.90      inference('sup-', [status(thm)], ['72', '88'])).
% 0.67/0.90  thf('90', plain,
% 0.67/0.90      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.67/0.90      inference('sup-', [status(thm)], ['1', '89'])).
% 0.67/0.90  thf(t66_xboole_1, axiom,
% 0.67/0.90    (![A:$i]:
% 0.67/0.90     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.67/0.90       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.67/0.90  thf('91', plain,
% 0.67/0.90      (![X28 : $i]: (((X28) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X28 @ X28))),
% 0.67/0.90      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.67/0.90  thf('92', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['90', '91'])).
% 0.67/0.90  thf('93', plain,
% 0.67/0.90      (![X13 : $i, X14 : $i]:
% 0.67/0.90         ((r1_tarski @ X13 @ X14)
% 0.67/0.90          | ((k4_xboole_0 @ X13 @ X14) != (k1_xboole_0)))),
% 0.67/0.90      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.67/0.90  thf('94', plain,
% 0.67/0.90      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.67/0.90      inference('sup-', [status(thm)], ['92', '93'])).
% 0.67/0.90  thf('95', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.67/0.90      inference('simplify', [status(thm)], ['94'])).
% 0.67/0.90  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 0.67/0.90  
% 0.67/0.90  % SZS output end Refutation
% 0.67/0.90  
% 0.67/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
