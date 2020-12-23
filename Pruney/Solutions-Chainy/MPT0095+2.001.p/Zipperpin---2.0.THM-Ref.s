%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vWOwej83QU

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:49 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 214 expanded)
%              Number of leaves         :   18 (  75 expanded)
%              Depth                    :   21
%              Number of atoms          :  736 (1636 expanded)
%              Number of equality atoms :   77 ( 181 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t88_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t88_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18
        = ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['6'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('49',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    r1_tarski @ k1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['22','54'])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','21','55'])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
     != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('65',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('69',plain,(
    r1_tarski @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('71',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['56','71','72','73'])).

thf('75',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('77',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['74','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vWOwej83QU
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:26:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 422 iterations in 0.211s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.67  thf(t88_xboole_1, conjecture,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( r1_xboole_0 @ A @ B ) =>
% 0.46/0.67       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i]:
% 0.46/0.67        ( ( r1_xboole_0 @ A @ B ) =>
% 0.46/0.67          ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t88_xboole_1])).
% 0.46/0.67  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(d7_xboole_0, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.46/0.67       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      (![X2 : $i, X3 : $i]:
% 0.46/0.67         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.46/0.67      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.46/0.67  thf('2', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.67  thf(t48_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      (![X19 : $i, X20 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.46/0.67           = (k3_xboole_0 @ X19 @ X20))),
% 0.46/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.67  thf(l32_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i]:
% 0.46/0.67         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.46/0.67          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.67        | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '5'])).
% 0.46/0.67  thf('7', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.67      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.67  thf(t45_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( r1_tarski @ A @ B ) =>
% 0.46/0.67       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (![X17 : $i, X18 : $i]:
% 0.46/0.67         (((X18) = (k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))
% 0.46/0.67          | ~ (r1_tarski @ X17 @ X18))),
% 0.46/0.67      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.46/0.67         = (k2_xboole_0 @ sk_A @ 
% 0.46/0.67            (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.67  thf(t41_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.67       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.46/0.67           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.67  thf(commutativity_k2_xboole_0, axiom,
% 0.46/0.67    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.46/0.67         = (k2_xboole_0 @ sk_A @ 
% 0.46/0.67            (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B))))),
% 0.46/0.67      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.46/0.67  thf('13', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.67  thf(t1_boole, axiom,
% 0.46/0.67    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.67  thf('14', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.46/0.67      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.67  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.67  thf(t40_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.67  thf('16', plain,
% 0.46/0.67      (![X12 : $i, X13 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.46/0.67           = (k4_xboole_0 @ X12 @ X13))),
% 0.46/0.67      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.46/0.67           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.46/0.67           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.67  thf('20', plain,
% 0.46/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.46/0.67           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.46/0.67           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.46/0.67      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.67  thf('23', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.67      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.67  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.67  thf(t11_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.46/0.67  thf('25', plain,
% 0.46/0.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.67         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.46/0.67      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ k1_xboole_0 @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.67  thf('27', plain, ((r1_tarski @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['23', '26'])).
% 0.46/0.67  thf('28', plain,
% 0.46/0.67      (![X5 : $i, X7 : $i]:
% 0.46/0.67         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.46/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      (((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.46/0.67         = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      (![X12 : $i, X13 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.46/0.67           = (k4_xboole_0 @ X12 @ X13))),
% 0.46/0.67      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.67  thf('31', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i]:
% 0.46/0.67         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.67  thf('32', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.46/0.67          | (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.67  thf('33', plain,
% 0.46/0.67      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.67        | (r1_tarski @ 
% 0.46/0.67           (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 0.46/0.67           (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['29', '32'])).
% 0.46/0.67  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.67  thf('35', plain,
% 0.46/0.67      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.67        | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.46/0.67           (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.67      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.67  thf('36', plain,
% 0.46/0.67      ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.67      inference('simplify', [status(thm)], ['35'])).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      (![X5 : $i, X7 : $i]:
% 0.46/0.67         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.46/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.67  thf('38', plain,
% 0.46/0.67      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.46/0.67         (k4_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.67  thf('39', plain,
% 0.46/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.46/0.67           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.67  thf('40', plain,
% 0.46/0.67      (((k4_xboole_0 @ sk_A @ 
% 0.46/0.67         (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))) = (k1_xboole_0))),
% 0.46/0.67      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.67  thf('41', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.67  thf('42', plain,
% 0.46/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.46/0.67           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.67  thf('43', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i]:
% 0.46/0.67         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.67  thf('44', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.46/0.67          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.67  thf('45', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.46/0.67          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['41', '44'])).
% 0.46/0.67  thf('46', plain,
% 0.46/0.67      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.67        | (r1_tarski @ (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 0.46/0.67           sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['40', '45'])).
% 0.46/0.67  thf('47', plain,
% 0.46/0.67      (![X19 : $i, X20 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.46/0.67           = (k3_xboole_0 @ X19 @ X20))),
% 0.46/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.67  thf('48', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.67  thf('49', plain,
% 0.46/0.67      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.46/0.67  thf('50', plain, ((r1_tarski @ k1_xboole_0 @ sk_B)),
% 0.46/0.67      inference('simplify', [status(thm)], ['49'])).
% 0.46/0.67  thf('51', plain,
% 0.46/0.67      (![X5 : $i, X7 : $i]:
% 0.46/0.67         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.46/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.67  thf('52', plain, (((k4_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.67  thf('53', plain,
% 0.46/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.46/0.67           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.67  thf('54', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.67           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.67  thf('55', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.67           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['22', '54'])).
% 0.46/0.67  thf('56', plain,
% 0.46/0.67      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.46/0.67         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ k1_xboole_0 @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['12', '21', '55'])).
% 0.46/0.67  thf('57', plain,
% 0.46/0.67      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.46/0.67         = (k2_xboole_0 @ sk_A @ 
% 0.46/0.67            (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B))))),
% 0.46/0.67      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.46/0.67  thf('58', plain,
% 0.46/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.67  thf('59', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.46/0.67          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['41', '44'])).
% 0.46/0.67  thf('60', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))
% 0.46/0.67            != (k1_xboole_0))
% 0.46/0.67          | (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.67  thf('61', plain,
% 0.46/0.67      (![X12 : $i, X13 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.46/0.67           = (k4_xboole_0 @ X12 @ X13))),
% 0.46/0.67      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.67  thf('62', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))
% 0.46/0.67            != (k1_xboole_0))
% 0.46/0.67          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.46/0.67      inference('demod', [status(thm)], ['60', '61'])).
% 0.46/0.67  thf('63', plain,
% 0.46/0.67      ((((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.46/0.67          != (k1_xboole_0))
% 0.46/0.67        | (r1_tarski @ 
% 0.46/0.67           (k4_xboole_0 @ sk_A @ 
% 0.46/0.67            (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B))) @ 
% 0.46/0.67           sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['57', '62'])).
% 0.46/0.67  thf('64', plain,
% 0.46/0.67      (((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.46/0.67         = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.67  thf('65', plain,
% 0.46/0.67      (![X19 : $i, X20 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.46/0.67           = (k3_xboole_0 @ X19 @ X20))),
% 0.46/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.67  thf('66', plain,
% 0.46/0.67      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.67        | (r1_tarski @ (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B)) @ 
% 0.46/0.67           sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.46/0.67  thf('67', plain,
% 0.46/0.67      ((r1_tarski @ (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B)) @ sk_A)),
% 0.46/0.67      inference('simplify', [status(thm)], ['66'])).
% 0.46/0.67  thf('68', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ k1_xboole_0 @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.67  thf('69', plain, ((r1_tarski @ k1_xboole_0 @ sk_A)),
% 0.46/0.67      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.67  thf('70', plain,
% 0.46/0.67      (![X5 : $i, X7 : $i]:
% 0.46/0.67         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.46/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.67  thf('71', plain, (((k4_xboole_0 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['69', '70'])).
% 0.46/0.67  thf('72', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.67  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.67  thf('74', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['56', '71', '72', '73'])).
% 0.46/0.67  thf('75', plain,
% 0.46/0.67      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B) != (sk_A))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('76', plain,
% 0.46/0.67      (![X12 : $i, X13 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.46/0.67           = (k4_xboole_0 @ X12 @ X13))),
% 0.46/0.67      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.67  thf('77', plain, (((k4_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.67  thf('78', plain, ($false),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['74', '77'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
