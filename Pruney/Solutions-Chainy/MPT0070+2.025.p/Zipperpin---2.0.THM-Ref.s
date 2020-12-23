%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RE4FIzkoNe

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:35 EST 2020

% Result     : Theorem 9.73s
% Output     : Refutation 9.73s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 497 expanded)
%              Number of leaves         :   19 ( 174 expanded)
%              Depth                    :   25
%              Number of atoms          : 1593 (4129 expanded)
%              Number of equality atoms :  149 ( 408 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('37',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('43',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) @ sk_B ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('45',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('49',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) @ sk_B )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('62',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['49','56','57','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('70',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['36','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ X0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_A ) ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['35','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ X1 @ X0 ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['22','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['21','79'])).

thf('81',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['84','87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','20'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('93',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('104',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('111',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['102','112','113'])).

thf('115',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('116',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('117',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('119',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['117','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('123',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('125',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('126',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('133',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('134',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('139',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('144',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['132','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['131','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['124','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) @ X0 ) @ sk_C ) ),
    inference('sup+',[status(thm)],['123','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ) ) @ sk_C ) ),
    inference('sup+',[status(thm)],['114','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('154',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('155',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['152','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ sk_C ) ),
    inference('sup+',[status(thm)],['92','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['91','163'])).

thf('165',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['90','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['89','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('172',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('174',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    $false ),
    inference(demod,[status(thm)],['0','175'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RE4FIzkoNe
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.73/9.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.73/9.98  % Solved by: fo/fo7.sh
% 9.73/9.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.73/9.98  % done 9101 iterations in 9.520s
% 9.73/9.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.73/9.98  % SZS output start Refutation
% 9.73/9.98  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 9.73/9.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.73/9.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.73/9.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.73/9.98  thf(sk_B_type, type, sk_B: $i).
% 9.73/9.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.73/9.98  thf(sk_C_type, type, sk_C: $i).
% 9.73/9.98  thf(sk_A_type, type, sk_A: $i).
% 9.73/9.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.73/9.98  thf(t63_xboole_1, conjecture,
% 9.73/9.98    (![A:$i,B:$i,C:$i]:
% 9.73/9.98     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 9.73/9.98       ( r1_xboole_0 @ A @ C ) ))).
% 9.73/9.98  thf(zf_stmt_0, negated_conjecture,
% 9.73/9.98    (~( ![A:$i,B:$i,C:$i]:
% 9.73/9.98        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 9.73/9.98          ( r1_xboole_0 @ A @ C ) ) )),
% 9.73/9.98    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 9.73/9.98  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 9.73/9.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.73/9.98  thf(commutativity_k3_xboole_0, axiom,
% 9.73/9.98    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 9.73/9.98  thf('1', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('2', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf(t48_xboole_1, axiom,
% 9.73/9.98    (![A:$i,B:$i]:
% 9.73/9.98     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 9.73/9.98  thf('3', plain,
% 9.73/9.98      (![X16 : $i, X17 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.73/9.98           = (k3_xboole_0 @ X16 @ X17))),
% 9.73/9.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.73/9.98  thf(t36_xboole_1, axiom,
% 9.73/9.98    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 9.73/9.98  thf('4', plain,
% 9.73/9.98      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 9.73/9.98      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.73/9.98  thf('5', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 9.73/9.98      inference('sup+', [status(thm)], ['3', '4'])).
% 9.73/9.98  thf('6', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 9.73/9.98      inference('sup+', [status(thm)], ['2', '5'])).
% 9.73/9.98  thf(l32_xboole_1, axiom,
% 9.73/9.98    (![A:$i,B:$i]:
% 9.73/9.98     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 9.73/9.98  thf('7', plain,
% 9.73/9.98      (![X5 : $i, X7 : $i]:
% 9.73/9.98         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 9.73/9.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.73/9.98  thf('8', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 9.73/9.98      inference('sup-', [status(thm)], ['6', '7'])).
% 9.73/9.98  thf('9', plain,
% 9.73/9.98      (![X16 : $i, X17 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.73/9.98           = (k3_xboole_0 @ X16 @ X17))),
% 9.73/9.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.73/9.98  thf('10', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 9.73/9.98           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 9.73/9.98      inference('sup+', [status(thm)], ['8', '9'])).
% 9.73/9.98  thf('11', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('12', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 9.73/9.98           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.73/9.98      inference('demod', [status(thm)], ['10', '11'])).
% 9.73/9.98  thf(t1_boole, axiom,
% 9.73/9.98    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 9.73/9.98  thf('13', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 9.73/9.98      inference('cnf', [status(esa)], [t1_boole])).
% 9.73/9.98  thf('14', plain,
% 9.73/9.98      (![X16 : $i, X17 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.73/9.98           = (k3_xboole_0 @ X16 @ X17))),
% 9.73/9.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.73/9.98  thf(t41_xboole_1, axiom,
% 9.73/9.98    (![A:$i,B:$i,C:$i]:
% 9.73/9.98     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 9.73/9.98       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 9.73/9.98  thf('15', plain,
% 9.73/9.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 9.73/9.98           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 9.73/9.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.73/9.98  thf('16', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 9.73/9.98           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 9.73/9.98      inference('sup+', [status(thm)], ['14', '15'])).
% 9.73/9.98  thf('17', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 9.73/9.98           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 9.73/9.98      inference('sup+', [status(thm)], ['13', '16'])).
% 9.73/9.98  thf('18', plain,
% 9.73/9.98      (![X16 : $i, X17 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.73/9.98           = (k3_xboole_0 @ X16 @ X17))),
% 9.73/9.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.73/9.98  thf('19', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 9.73/9.98           = (k3_xboole_0 @ X1 @ X0))),
% 9.73/9.98      inference('demod', [status(thm)], ['17', '18'])).
% 9.73/9.98  thf('20', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ X1 @ X0)
% 9.73/9.98           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.73/9.98      inference('demod', [status(thm)], ['12', '19'])).
% 9.73/9.98  thf('21', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ X0 @ X1)
% 9.73/9.98           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.73/9.98      inference('sup+', [status(thm)], ['1', '20'])).
% 9.73/9.98  thf('22', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 9.73/9.98           = (k3_xboole_0 @ X1 @ X0))),
% 9.73/9.98      inference('demod', [status(thm)], ['17', '18'])).
% 9.73/9.98  thf('23', plain,
% 9.73/9.98      (![X16 : $i, X17 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.73/9.98           = (k3_xboole_0 @ X16 @ X17))),
% 9.73/9.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.73/9.98  thf(t39_xboole_1, axiom,
% 9.73/9.98    (![A:$i,B:$i]:
% 9.73/9.98     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 9.73/9.98  thf('24', plain,
% 9.73/9.98      (![X11 : $i, X12 : $i]:
% 9.73/9.98         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 9.73/9.98           = (k2_xboole_0 @ X11 @ X12))),
% 9.73/9.98      inference('cnf', [status(esa)], [t39_xboole_1])).
% 9.73/9.98  thf('25', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 9.73/9.98           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 9.73/9.98      inference('sup+', [status(thm)], ['23', '24'])).
% 9.73/9.98  thf('26', plain,
% 9.73/9.98      (![X16 : $i, X17 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.73/9.98           = (k3_xboole_0 @ X16 @ X17))),
% 9.73/9.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.73/9.98  thf('27', plain,
% 9.73/9.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 9.73/9.98           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 9.73/9.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.73/9.98  thf('28', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 9.73/9.98           = (k4_xboole_0 @ X2 @ 
% 9.73/9.98              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 9.73/9.98      inference('sup+', [status(thm)], ['26', '27'])).
% 9.73/9.98  thf('29', plain,
% 9.73/9.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 9.73/9.98           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 9.73/9.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.73/9.98  thf('30', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 9.73/9.98           = (k4_xboole_0 @ X2 @ 
% 9.73/9.98              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 9.73/9.98      inference('demod', [status(thm)], ['28', '29'])).
% 9.73/9.98  thf('31', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 9.73/9.98           (k3_xboole_0 @ X0 @ X1))
% 9.73/9.98           = (k4_xboole_0 @ X2 @ 
% 9.73/9.98              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 9.73/9.98               (k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))))),
% 9.73/9.98      inference('sup+', [status(thm)], ['25', '30'])).
% 9.73/9.98  thf('32', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('33', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 9.73/9.98           = (k4_xboole_0 @ X2 @ 
% 9.73/9.98              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 9.73/9.98      inference('demod', [status(thm)], ['28', '29'])).
% 9.73/9.98  thf('34', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('35', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 9.73/9.98           (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 9.73/9.98           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))))),
% 9.73/9.98      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 9.73/9.98  thf('36', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 9.73/9.98           = (k4_xboole_0 @ X2 @ 
% 9.73/9.98              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 9.73/9.98      inference('demod', [status(thm)], ['28', '29'])).
% 9.73/9.98  thf('37', plain, ((r1_tarski @ sk_A @ sk_B)),
% 9.73/9.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.73/9.98  thf('38', plain,
% 9.73/9.98      (![X5 : $i, X7 : $i]:
% 9.73/9.98         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 9.73/9.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.73/9.98  thf('39', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 9.73/9.98      inference('sup-', [status(thm)], ['37', '38'])).
% 9.73/9.98  thf('40', plain,
% 9.73/9.98      (![X16 : $i, X17 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.73/9.98           = (k3_xboole_0 @ X16 @ X17))),
% 9.73/9.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.73/9.98  thf('41', plain,
% 9.73/9.98      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 9.73/9.98      inference('sup+', [status(thm)], ['39', '40'])).
% 9.73/9.98  thf('42', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 9.73/9.98      inference('sup+', [status(thm)], ['2', '5'])).
% 9.73/9.98  thf('43', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ k1_xboole_0) @ sk_B)),
% 9.73/9.98      inference('sup+', [status(thm)], ['41', '42'])).
% 9.73/9.98  thf('44', plain,
% 9.73/9.98      (![X5 : $i, X7 : $i]:
% 9.73/9.98         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 9.73/9.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.73/9.98  thf('45', plain,
% 9.73/9.98      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ k1_xboole_0) @ sk_B)
% 9.73/9.98         = (k1_xboole_0))),
% 9.73/9.98      inference('sup-', [status(thm)], ['43', '44'])).
% 9.73/9.98  thf('46', plain,
% 9.73/9.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 9.73/9.98           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 9.73/9.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.73/9.98  thf('47', plain,
% 9.73/9.98      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ k1_xboole_0 @ sk_B))
% 9.73/9.98         = (k1_xboole_0))),
% 9.73/9.98      inference('demod', [status(thm)], ['45', '46'])).
% 9.73/9.98  thf('48', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 9.73/9.98           = (k4_xboole_0 @ X2 @ 
% 9.73/9.98              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 9.73/9.98      inference('demod', [status(thm)], ['28', '29'])).
% 9.73/9.98  thf('49', plain,
% 9.73/9.98      (((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ k1_xboole_0) @ sk_B)
% 9.73/9.98         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 9.73/9.98      inference('sup+', [status(thm)], ['47', '48'])).
% 9.73/9.98  thf('50', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 9.73/9.98      inference('cnf', [status(esa)], [t1_boole])).
% 9.73/9.98  thf(t7_xboole_1, axiom,
% 9.73/9.98    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 9.73/9.98  thf('51', plain,
% 9.73/9.98      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 9.73/9.98      inference('cnf', [status(esa)], [t7_xboole_1])).
% 9.73/9.98  thf('52', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 9.73/9.98      inference('sup+', [status(thm)], ['50', '51'])).
% 9.73/9.98  thf('53', plain,
% 9.73/9.98      (![X5 : $i, X7 : $i]:
% 9.73/9.98         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 9.73/9.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.73/9.98  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.73/9.98      inference('sup-', [status(thm)], ['52', '53'])).
% 9.73/9.98  thf('55', plain,
% 9.73/9.98      (![X16 : $i, X17 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.73/9.98           = (k3_xboole_0 @ X16 @ X17))),
% 9.73/9.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.73/9.98  thf('56', plain,
% 9.73/9.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 9.73/9.98      inference('sup+', [status(thm)], ['54', '55'])).
% 9.73/9.98  thf('57', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.73/9.98      inference('sup-', [status(thm)], ['52', '53'])).
% 9.73/9.98  thf('59', plain,
% 9.73/9.98      (![X11 : $i, X12 : $i]:
% 9.73/9.98         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 9.73/9.98           = (k2_xboole_0 @ X11 @ X12))),
% 9.73/9.98      inference('cnf', [status(esa)], [t39_xboole_1])).
% 9.73/9.98  thf('60', plain,
% 9.73/9.98      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 9.73/9.98      inference('sup+', [status(thm)], ['58', '59'])).
% 9.73/9.98  thf('61', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 9.73/9.98      inference('cnf', [status(esa)], [t1_boole])).
% 9.73/9.98  thf('62', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 9.73/9.98      inference('demod', [status(thm)], ['60', '61'])).
% 9.73/9.98  thf('63', plain,
% 9.73/9.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 9.73/9.98      inference('sup+', [status(thm)], ['54', '55'])).
% 9.73/9.98  thf('64', plain,
% 9.73/9.98      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_A))
% 9.73/9.98         = (k3_xboole_0 @ sk_A @ sk_A))),
% 9.73/9.98      inference('demod', [status(thm)], ['49', '56', '57', '62', '63'])).
% 9.73/9.98  thf('65', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 9.73/9.98           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 9.73/9.98      inference('sup+', [status(thm)], ['14', '15'])).
% 9.73/9.98  thf('66', plain,
% 9.73/9.98      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 9.73/9.98      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.73/9.98  thf('67', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         (r1_tarski @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ X2)),
% 9.73/9.98      inference('sup+', [status(thm)], ['65', '66'])).
% 9.73/9.98  thf('68', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         (r1_tarski @ (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_A) @ X0) @ sk_B)),
% 9.73/9.98      inference('sup+', [status(thm)], ['64', '67'])).
% 9.73/9.98  thf('69', plain,
% 9.73/9.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 9.73/9.98      inference('sup+', [status(thm)], ['54', '55'])).
% 9.73/9.98  thf('70', plain,
% 9.73/9.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 9.73/9.98           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 9.73/9.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.73/9.98  thf('71', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X1)
% 9.73/9.98           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 9.73/9.98      inference('sup+', [status(thm)], ['69', '70'])).
% 9.73/9.98  thf('72', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         (r1_tarski @ 
% 9.73/9.98          (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ k1_xboole_0 @ X0)) @ sk_B)),
% 9.73/9.98      inference('demod', [status(thm)], ['68', '71'])).
% 9.73/9.98  thf('73', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         (r1_tarski @ 
% 9.73/9.98          (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ k1_xboole_0) @ X0) @ sk_B)),
% 9.73/9.98      inference('sup+', [status(thm)], ['36', '72'])).
% 9.73/9.98  thf('74', plain,
% 9.73/9.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 9.73/9.98      inference('sup+', [status(thm)], ['54', '55'])).
% 9.73/9.98  thf('75', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_A) @ X0) @ sk_B)),
% 9.73/9.98      inference('demod', [status(thm)], ['73', '74'])).
% 9.73/9.98  thf('76', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         (r1_tarski @ 
% 9.73/9.98          (k3_xboole_0 @ sk_A @ 
% 9.73/9.98           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_A))) @ 
% 9.73/9.98          sk_B)),
% 9.73/9.98      inference('sup+', [status(thm)], ['35', '75'])).
% 9.73/9.98  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.73/9.98      inference('sup-', [status(thm)], ['52', '53'])).
% 9.73/9.98  thf('78', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         (r1_tarski @ 
% 9.73/9.98          (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ k1_xboole_0)) @ sk_B)),
% 9.73/9.98      inference('demod', [status(thm)], ['76', '77'])).
% 9.73/9.98  thf('79', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         (r1_tarski @ (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ X1 @ X0)) @ sk_B)),
% 9.73/9.98      inference('sup+', [status(thm)], ['22', '78'])).
% 9.73/9.98  thf('80', plain,
% 9.73/9.98      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B)),
% 9.73/9.98      inference('sup+', [status(thm)], ['21', '79'])).
% 9.73/9.98  thf('81', plain,
% 9.73/9.98      (![X5 : $i, X7 : $i]:
% 9.73/9.98         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 9.73/9.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.73/9.98  thf('82', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B) = (k1_xboole_0))),
% 9.73/9.98      inference('sup-', [status(thm)], ['80', '81'])).
% 9.73/9.98  thf('83', plain,
% 9.73/9.98      (![X16 : $i, X17 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.73/9.98           = (k3_xboole_0 @ X16 @ X17))),
% 9.73/9.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.73/9.98  thf('84', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ k1_xboole_0)
% 9.73/9.98           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B))),
% 9.73/9.98      inference('sup+', [status(thm)], ['82', '83'])).
% 9.73/9.98  thf('85', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('86', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 9.73/9.98           = (k3_xboole_0 @ X1 @ X0))),
% 9.73/9.98      inference('demod', [status(thm)], ['17', '18'])).
% 9.73/9.98  thf('87', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 9.73/9.98           = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('sup+', [status(thm)], ['85', '86'])).
% 9.73/9.98  thf('88', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('89', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ sk_A @ X0)
% 9.73/9.98           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 9.73/9.98      inference('demod', [status(thm)], ['84', '87', '88'])).
% 9.73/9.98  thf('90', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('91', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ X0 @ X1)
% 9.73/9.98           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.73/9.98      inference('sup+', [status(thm)], ['1', '20'])).
% 9.73/9.98  thf('92', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 9.73/9.98           = (k3_xboole_0 @ X1 @ X0))),
% 9.73/9.98      inference('demod', [status(thm)], ['17', '18'])).
% 9.73/9.98  thf('93', plain,
% 9.73/9.98      (![X16 : $i, X17 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.73/9.98           = (k3_xboole_0 @ X16 @ X17))),
% 9.73/9.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.73/9.98  thf('94', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 9.73/9.98           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 9.73/9.98      inference('sup+', [status(thm)], ['23', '24'])).
% 9.73/9.98  thf('95', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 9.73/9.98           (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 9.73/9.98           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 9.73/9.98      inference('sup+', [status(thm)], ['93', '94'])).
% 9.73/9.98  thf('96', plain,
% 9.73/9.98      (![X16 : $i, X17 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.73/9.98           = (k3_xboole_0 @ X16 @ X17))),
% 9.73/9.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.73/9.98  thf('97', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 9.73/9.98           (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 9.73/9.98           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 9.73/9.98      inference('demod', [status(thm)], ['95', '96'])).
% 9.73/9.98  thf('98', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 9.73/9.98           = (k4_xboole_0 @ X2 @ 
% 9.73/9.98              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 9.73/9.98      inference('demod', [status(thm)], ['28', '29'])).
% 9.73/9.98  thf('99', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 9.73/9.98           (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 9.73/9.98           = (k4_xboole_0 @ X2 @ 
% 9.73/9.98              (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 9.73/9.98               (k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)))))),
% 9.73/9.98      inference('sup+', [status(thm)], ['97', '98'])).
% 9.73/9.98  thf('100', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 9.73/9.98           = (k4_xboole_0 @ X2 @ 
% 9.73/9.98              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 9.73/9.98      inference('demod', [status(thm)], ['28', '29'])).
% 9.73/9.98  thf('101', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('102', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 9.73/9.98           (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 9.73/9.98           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1))))),
% 9.73/9.98      inference('demod', [status(thm)], ['99', '100', '101'])).
% 9.73/9.98  thf('103', plain,
% 9.73/9.98      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 9.73/9.98      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.73/9.98  thf('104', plain,
% 9.73/9.98      (![X5 : $i, X7 : $i]:
% 9.73/9.98         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 9.73/9.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.73/9.98  thf('105', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 9.73/9.98      inference('sup-', [status(thm)], ['103', '104'])).
% 9.73/9.98  thf('106', plain,
% 9.73/9.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 9.73/9.98           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 9.73/9.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.73/9.98  thf('107', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 9.73/9.98      inference('demod', [status(thm)], ['105', '106'])).
% 9.73/9.98  thf('108', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 9.73/9.98           = (k4_xboole_0 @ X2 @ 
% 9.73/9.98              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 9.73/9.98      inference('demod', [status(thm)], ['28', '29'])).
% 9.73/9.98  thf('109', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 9.73/9.98           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ k1_xboole_0)))),
% 9.73/9.98      inference('sup+', [status(thm)], ['107', '108'])).
% 9.73/9.98  thf('110', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('111', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 9.73/9.98      inference('cnf', [status(esa)], [t1_boole])).
% 9.73/9.98  thf('112', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 9.73/9.98           = (k4_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('demod', [status(thm)], ['109', '110', '111'])).
% 9.73/9.98  thf('113', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('114', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 9.73/9.98           (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))
% 9.73/9.98           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1))))),
% 9.73/9.98      inference('demod', [status(thm)], ['102', '112', '113'])).
% 9.73/9.98  thf('115', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 9.73/9.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.73/9.98  thf(d7_xboole_0, axiom,
% 9.73/9.98    (![A:$i,B:$i]:
% 9.73/9.98     ( ( r1_xboole_0 @ A @ B ) <=>
% 9.73/9.98       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 9.73/9.98  thf('116', plain,
% 9.73/9.98      (![X2 : $i, X3 : $i]:
% 9.73/9.98         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 9.73/9.98      inference('cnf', [status(esa)], [d7_xboole_0])).
% 9.73/9.98  thf('117', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 9.73/9.98      inference('sup-', [status(thm)], ['115', '116'])).
% 9.73/9.98  thf('118', plain,
% 9.73/9.98      (![X16 : $i, X17 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.73/9.98           = (k3_xboole_0 @ X16 @ X17))),
% 9.73/9.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.73/9.98  thf('119', plain,
% 9.73/9.98      (![X16 : $i, X17 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.73/9.98           = (k3_xboole_0 @ X16 @ X17))),
% 9.73/9.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.73/9.98  thf('120', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 9.73/9.98           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 9.73/9.98      inference('sup+', [status(thm)], ['118', '119'])).
% 9.73/9.98  thf('121', plain,
% 9.73/9.98      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 9.73/9.98         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 9.73/9.98      inference('sup+', [status(thm)], ['117', '120'])).
% 9.73/9.98  thf('122', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 9.73/9.98           = (k4_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('demod', [status(thm)], ['109', '110', '111'])).
% 9.73/9.98  thf('123', plain,
% 9.73/9.98      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_C))),
% 9.73/9.98      inference('demod', [status(thm)], ['121', '122'])).
% 9.73/9.98  thf('124', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 9.73/9.98           = (k4_xboole_0 @ X2 @ 
% 9.73/9.98              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 9.73/9.98      inference('demod', [status(thm)], ['28', '29'])).
% 9.73/9.98  thf('125', plain,
% 9.73/9.98      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 9.73/9.98      inference('cnf', [status(esa)], [t7_xboole_1])).
% 9.73/9.98  thf('126', plain,
% 9.73/9.98      (![X5 : $i, X7 : $i]:
% 9.73/9.98         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 9.73/9.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.73/9.98  thf('127', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 9.73/9.98      inference('sup-', [status(thm)], ['125', '126'])).
% 9.73/9.98  thf('128', plain,
% 9.73/9.98      (![X11 : $i, X12 : $i]:
% 9.73/9.98         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 9.73/9.98           = (k2_xboole_0 @ X11 @ X12))),
% 9.73/9.98      inference('cnf', [status(esa)], [t39_xboole_1])).
% 9.73/9.98  thf('129', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 9.73/9.98           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 9.73/9.98      inference('sup+', [status(thm)], ['127', '128'])).
% 9.73/9.98  thf('130', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 9.73/9.98      inference('cnf', [status(esa)], [t1_boole])).
% 9.73/9.98  thf('131', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k2_xboole_0 @ X0 @ X1)
% 9.73/9.98           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 9.73/9.98      inference('demod', [status(thm)], ['129', '130'])).
% 9.73/9.98  thf('132', plain,
% 9.73/9.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 9.73/9.98           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 9.73/9.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.73/9.98  thf('133', plain,
% 9.73/9.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 9.73/9.98           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 9.73/9.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.73/9.98  thf('134', plain,
% 9.73/9.98      (![X11 : $i, X12 : $i]:
% 9.73/9.98         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 9.73/9.98           = (k2_xboole_0 @ X11 @ X12))),
% 9.73/9.98      inference('cnf', [status(esa)], [t39_xboole_1])).
% 9.73/9.98  thf('135', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 9.73/9.98           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 9.73/9.98      inference('sup+', [status(thm)], ['133', '134'])).
% 9.73/9.98  thf('136', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 9.73/9.98           = (k4_xboole_0 @ X2 @ 
% 9.73/9.98              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 9.73/9.98      inference('demod', [status(thm)], ['28', '29'])).
% 9.73/9.98  thf('137', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 9.73/9.98           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 9.73/9.98      inference('sup+', [status(thm)], ['135', '136'])).
% 9.73/9.98  thf('138', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('139', plain,
% 9.73/9.98      (![X11 : $i, X12 : $i]:
% 9.73/9.98         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 9.73/9.98           = (k2_xboole_0 @ X11 @ X12))),
% 9.73/9.98      inference('cnf', [status(esa)], [t39_xboole_1])).
% 9.73/9.98  thf('140', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 9.73/9.98           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 9.73/9.98      inference('demod', [status(thm)], ['137', '138', '139'])).
% 9.73/9.98  thf('141', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 9.73/9.98      inference('demod', [status(thm)], ['105', '106'])).
% 9.73/9.98  thf('142', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 9.73/9.98      inference('demod', [status(thm)], ['140', '141'])).
% 9.73/9.98  thf('143', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('144', plain,
% 9.73/9.98      (![X2 : $i, X4 : $i]:
% 9.73/9.98         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 9.73/9.98      inference('cnf', [status(esa)], [d7_xboole_0])).
% 9.73/9.98  thf('145', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('sup-', [status(thm)], ['143', '144'])).
% 9.73/9.98  thf('146', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         (((k1_xboole_0) != (k1_xboole_0))
% 9.73/9.98          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 9.73/9.98      inference('sup-', [status(thm)], ['142', '145'])).
% 9.73/9.98  thf('147', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 9.73/9.98      inference('simplify', [status(thm)], ['146'])).
% 9.73/9.98  thf('148', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)),
% 9.73/9.98      inference('sup+', [status(thm)], ['132', '147'])).
% 9.73/9.98  thf('149', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)),
% 9.73/9.98      inference('sup+', [status(thm)], ['131', '148'])).
% 9.73/9.98  thf('150', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.73/9.98         (r1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X1)),
% 9.73/9.98      inference('sup+', [status(thm)], ['124', '149'])).
% 9.73/9.98  thf('151', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         (r1_xboole_0 @ 
% 9.73/9.98          (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ k1_xboole_0) @ X0) @ sk_C)),
% 9.73/9.98      inference('sup+', [status(thm)], ['123', '150'])).
% 9.73/9.98  thf('152', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         (r1_xboole_0 @ 
% 9.73/9.98          (k3_xboole_0 @ sk_B @ 
% 9.73/9.98           (k4_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ k1_xboole_0))) @ 
% 9.73/9.98          sk_C)),
% 9.73/9.98      inference('sup+', [status(thm)], ['114', '151'])).
% 9.73/9.98  thf('153', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.73/9.98      inference('sup-', [status(thm)], ['52', '53'])).
% 9.73/9.98  thf('154', plain,
% 9.73/9.98      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 9.73/9.98      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.73/9.98  thf('155', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 9.73/9.98      inference('sup+', [status(thm)], ['153', '154'])).
% 9.73/9.98  thf('156', plain,
% 9.73/9.98      (![X5 : $i, X7 : $i]:
% 9.73/9.98         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 9.73/9.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.73/9.98  thf('157', plain,
% 9.73/9.98      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 9.73/9.98      inference('sup-', [status(thm)], ['155', '156'])).
% 9.73/9.98  thf('158', plain,
% 9.73/9.98      (![X16 : $i, X17 : $i]:
% 9.73/9.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.73/9.98           = (k3_xboole_0 @ X16 @ X17))),
% 9.73/9.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.73/9.98  thf('159', plain,
% 9.73/9.98      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 9.73/9.98      inference('sup+', [status(thm)], ['157', '158'])).
% 9.73/9.98  thf('160', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('161', plain,
% 9.73/9.98      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 9.73/9.98      inference('sup+', [status(thm)], ['159', '160'])).
% 9.73/9.98  thf('162', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         (r1_xboole_0 @ 
% 9.73/9.98          (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ k1_xboole_0)) @ sk_C)),
% 9.73/9.98      inference('demod', [status(thm)], ['152', '161'])).
% 9.73/9.98  thf('163', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X1 @ X0)) @ sk_C)),
% 9.73/9.98      inference('sup+', [status(thm)], ['92', '162'])).
% 9.73/9.98  thf('164', plain,
% 9.73/9.98      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_C)),
% 9.73/9.98      inference('sup+', [status(thm)], ['91', '163'])).
% 9.73/9.98  thf('165', plain,
% 9.73/9.98      (![X2 : $i, X3 : $i]:
% 9.73/9.98         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 9.73/9.98      inference('cnf', [status(esa)], [d7_xboole_0])).
% 9.73/9.98  thf('166', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_C) = (k1_xboole_0))),
% 9.73/9.98      inference('sup-', [status(thm)], ['164', '165'])).
% 9.73/9.98  thf('167', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.73/9.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.73/9.98  thf('168', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 9.73/9.98      inference('demod', [status(thm)], ['166', '167'])).
% 9.73/9.98  thf('169', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ X0)) = (k1_xboole_0))),
% 9.73/9.98      inference('sup+', [status(thm)], ['90', '168'])).
% 9.73/9.98  thf('170', plain,
% 9.73/9.98      (![X0 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))),
% 9.73/9.98      inference('sup+', [status(thm)], ['89', '169'])).
% 9.73/9.98  thf('171', plain,
% 9.73/9.98      (![X0 : $i, X1 : $i]:
% 9.73/9.98         ((k3_xboole_0 @ X1 @ X0)
% 9.73/9.98           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.73/9.98      inference('demod', [status(thm)], ['12', '19'])).
% 9.73/9.98  thf('172', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 9.73/9.98      inference('sup+', [status(thm)], ['170', '171'])).
% 9.73/9.98  thf('173', plain,
% 9.73/9.98      (![X2 : $i, X4 : $i]:
% 9.73/9.98         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 9.73/9.98      inference('cnf', [status(esa)], [d7_xboole_0])).
% 9.73/9.98  thf('174', plain,
% 9.73/9.98      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C))),
% 9.73/9.98      inference('sup-', [status(thm)], ['172', '173'])).
% 9.73/9.98  thf('175', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 9.73/9.98      inference('simplify', [status(thm)], ['174'])).
% 9.73/9.98  thf('176', plain, ($false), inference('demod', [status(thm)], ['0', '175'])).
% 9.73/9.98  
% 9.73/9.98  % SZS output end Refutation
% 9.73/9.98  
% 9.73/9.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
