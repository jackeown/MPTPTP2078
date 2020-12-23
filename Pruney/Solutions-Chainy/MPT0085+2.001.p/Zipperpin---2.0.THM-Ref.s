%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MQBhNK7Bb8

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:25 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 184 expanded)
%              Number of leaves         :   23 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :  636 (1326 expanded)
%              Number of equality atoms :   65 ( 157 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(t78_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          = ( k3_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
 != ( k3_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
 != ( k3_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['3','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_A )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('48',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('56',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['41','52','53','54','55'])).

thf('57',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('58',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ( k3_xboole_0 @ sk_C_2 @ sk_A )
 != ( k3_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['2','62','63'])).

thf('65',plain,(
    $false ),
    inference(simplify,[status(thm)],['64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MQBhNK7Bb8
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:19:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.76/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.98  % Solved by: fo/fo7.sh
% 0.76/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.98  % done 1285 iterations in 0.527s
% 0.76/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.98  % SZS output start Refutation
% 0.76/0.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.98  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.76/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.98  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.76/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.98  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.76/0.98  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.76/0.98  thf(t78_xboole_1, conjecture,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( r1_xboole_0 @ A @ B ) =>
% 0.76/0.98       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.76/0.98         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.76/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.98    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.98        ( ( r1_xboole_0 @ A @ B ) =>
% 0.76/0.98          ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.76/0.98            ( k3_xboole_0 @ A @ C ) ) ) )),
% 0.76/0.98    inference('cnf.neg', [status(esa)], [t78_xboole_1])).
% 0.76/0.98  thf('0', plain,
% 0.76/0.98      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.76/0.98         != (k3_xboole_0 @ sk_A @ sk_C_2))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(commutativity_k3_xboole_0, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.76/0.98  thf('1', plain,
% 0.76/0.98      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.98  thf('2', plain,
% 0.76/0.98      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.76/0.98         != (k3_xboole_0 @ sk_C_2 @ sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['0', '1'])).
% 0.76/0.98  thf('3', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(t4_xboole_0, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.76/0.98            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.76/0.98       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.76/0.98            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.76/0.98  thf('4', plain,
% 0.76/0.98      (![X8 : $i, X9 : $i]:
% 0.76/0.98         ((r1_xboole_0 @ X8 @ X9)
% 0.76/0.98          | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.76/0.98  thf('5', plain,
% 0.76/0.98      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.98  thf('6', plain,
% 0.76/0.98      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.76/0.98         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.76/0.98          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.76/0.98      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.76/0.98  thf('7', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.98          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.76/0.98      inference('sup-', [status(thm)], ['5', '6'])).
% 0.76/0.98  thf('8', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.76/0.98      inference('sup-', [status(thm)], ['4', '7'])).
% 0.76/0.98  thf('9', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.76/0.98      inference('sup-', [status(thm)], ['3', '8'])).
% 0.76/0.98  thf(d3_tarski, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( r1_tarski @ A @ B ) <=>
% 0.76/0.98       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.76/0.98  thf('10', plain,
% 0.76/0.98      (![X5 : $i, X7 : $i]:
% 0.76/0.98         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.76/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.98  thf('11', plain,
% 0.76/0.98      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.76/0.98         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.76/0.98          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.76/0.98      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.76/0.98  thf('12', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.76/0.98          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['10', '11'])).
% 0.76/0.98  thf('13', plain,
% 0.76/0.98      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['9', '12'])).
% 0.76/0.98  thf(t12_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.76/0.98  thf('14', plain,
% 0.76/0.98      (![X12 : $i, X13 : $i]:
% 0.76/0.98         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.76/0.98      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.98  thf('15', plain,
% 0.76/0.98      (![X0 : $i]: ((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0) = (X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.98  thf(t2_boole, axiom,
% 0.76/0.98    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.76/0.98  thf('16', plain,
% 0.76/0.98      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('cnf', [status(esa)], [t2_boole])).
% 0.76/0.98  thf(t22_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.76/0.98  thf('17', plain,
% 0.76/0.98      (![X14 : $i, X15 : $i]:
% 0.76/0.98         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 0.76/0.98      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.76/0.98  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['16', '17'])).
% 0.76/0.98  thf('19', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.76/0.98      inference('sup+', [status(thm)], ['15', '18'])).
% 0.76/0.98  thf('20', plain,
% 0.76/0.98      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.98  thf(t48_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/0.98  thf('21', plain,
% 0.76/0.98      (![X22 : $i, X23 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.76/0.98           = (k3_xboole_0 @ X22 @ X23))),
% 0.76/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.98  thf('22', plain,
% 0.76/0.98      (![X22 : $i, X23 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.76/0.98           = (k3_xboole_0 @ X22 @ X23))),
% 0.76/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.98  thf('23', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.98           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.98      inference('sup+', [status(thm)], ['21', '22'])).
% 0.76/0.98  thf('24', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.98           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.98      inference('sup+', [status(thm)], ['20', '23'])).
% 0.76/0.98  thf('25', plain,
% 0.76/0.98      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.76/0.98         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('sup+', [status(thm)], ['19', '24'])).
% 0.76/0.98  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['16', '17'])).
% 0.76/0.98  thf(commutativity_k2_xboole_0, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.76/0.98  thf('27', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.98  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['26', '27'])).
% 0.76/0.98  thf(t39_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.76/0.98  thf('29', plain,
% 0.76/0.98      (![X17 : $i, X18 : $i]:
% 0.76/0.98         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.76/0.98           = (k2_xboole_0 @ X17 @ X18))),
% 0.76/0.98      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.76/0.98  thf('30', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['28', '29'])).
% 0.76/0.98  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['26', '27'])).
% 0.76/0.98  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['30', '31'])).
% 0.76/0.98  thf('33', plain,
% 0.76/0.98      (((sk_A) = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('demod', [status(thm)], ['25', '32'])).
% 0.76/0.98  thf('34', plain,
% 0.76/0.98      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.98  thf('35', plain,
% 0.76/0.98      (![X22 : $i, X23 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.76/0.98           = (k3_xboole_0 @ X22 @ X23))),
% 0.76/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.98  thf('36', plain,
% 0.76/0.98      (![X17 : $i, X18 : $i]:
% 0.76/0.98         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.76/0.98           = (k2_xboole_0 @ X17 @ X18))),
% 0.76/0.98      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.76/0.98  thf('37', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.98           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.76/0.98      inference('sup+', [status(thm)], ['35', '36'])).
% 0.76/0.98  thf('38', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.98  thf('39', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.98           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['37', '38'])).
% 0.76/0.98  thf('40', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.98           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.98      inference('sup+', [status(thm)], ['34', '39'])).
% 0.76/0.98  thf('41', plain,
% 0.76/0.98      (((k2_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A) @ 
% 0.76/0.98         sk_A)
% 0.76/0.98         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.76/0.98            (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)))),
% 0.76/0.98      inference('sup+', [status(thm)], ['33', '40'])).
% 0.76/0.98  thf('42', plain,
% 0.76/0.98      (![X17 : $i, X18 : $i]:
% 0.76/0.98         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.76/0.98           = (k2_xboole_0 @ X17 @ X18))),
% 0.76/0.98      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.76/0.98  thf(t41_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.76/0.98       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.76/0.98  thf('43', plain,
% 0.76/0.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.76/0.98           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.98  thf('44', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 0.76/0.98           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.76/0.98      inference('sup+', [status(thm)], ['42', '43'])).
% 0.76/0.98  thf('45', plain,
% 0.76/0.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.76/0.98           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.98  thf('46', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 0.76/0.98           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.76/0.98      inference('demod', [status(thm)], ['44', '45'])).
% 0.76/0.98  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['30', '31'])).
% 0.76/0.98  thf('48', plain,
% 0.76/0.98      (![X22 : $i, X23 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.76/0.98           = (k3_xboole_0 @ X22 @ X23))),
% 0.76/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.98  thf('49', plain,
% 0.76/0.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['47', '48'])).
% 0.76/0.98  thf('50', plain,
% 0.76/0.98      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('cnf', [status(esa)], [t2_boole])).
% 0.76/0.98  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/0.98      inference('demod', [status(thm)], ['49', '50'])).
% 0.76/0.98  thf('52', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['46', '51'])).
% 0.76/0.98  thf('53', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['26', '27'])).
% 0.76/0.98  thf('54', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['46', '51'])).
% 0.76/0.98  thf('55', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['16', '17'])).
% 0.76/0.98  thf('56', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['41', '52', '53', '54', '55'])).
% 0.76/0.98  thf('57', plain,
% 0.76/0.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.76/0.98           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.98  thf('58', plain,
% 0.76/0.98      (![X22 : $i, X23 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.76/0.98           = (k3_xboole_0 @ X22 @ X23))),
% 0.76/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.98  thf('59', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.76/0.98           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.76/0.98      inference('sup+', [status(thm)], ['57', '58'])).
% 0.76/0.98  thf('60', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 0.76/0.98           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.76/0.98      inference('sup+', [status(thm)], ['56', '59'])).
% 0.76/0.98  thf('61', plain,
% 0.76/0.98      (![X22 : $i, X23 : $i]:
% 0.76/0.98         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.76/0.98           = (k3_xboole_0 @ X22 @ X23))),
% 0.76/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.98  thf('62', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((k3_xboole_0 @ sk_A @ X0)
% 0.76/0.98           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['60', '61'])).
% 0.76/0.98  thf('63', plain,
% 0.76/0.98      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.98  thf('64', plain,
% 0.76/0.98      (((k3_xboole_0 @ sk_C_2 @ sk_A) != (k3_xboole_0 @ sk_C_2 @ sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['2', '62', '63'])).
% 0.76/0.98  thf('65', plain, ($false), inference('simplify', [status(thm)], ['64'])).
% 0.76/0.98  
% 0.76/0.98  % SZS output end Refutation
% 0.76/0.98  
% 0.76/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
