%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EzV6Hw5TtS

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:52 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 592 expanded)
%              Number of leaves         :   17 ( 176 expanded)
%              Depth                    :   22
%              Number of atoms          : 1082 (6357 expanded)
%              Number of equality atoms :   89 ( 382 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t70_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
                & ( r1_xboole_0 @ A @ C ) )
            & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
            & ( r1_xboole_0 @ A @ B )
            & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_xboole_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('11',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('15',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
        = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ X0 )
        = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( ( r1_xboole_0 @ sk_A @ sk_B )
      & ( r1_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','23'])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_A @ sk_B )
      & ( r1_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['8'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('39',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('44',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('49',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('50',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_xboole_0 @ sk_C @ sk_A )
      = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('56',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('58',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_A ) ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('65',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('67',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_B ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['3','4','27','47','48','70'])).

thf('72',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','71'])).

thf('73',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('74',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['3','4','27','47','48'])).

thf('75',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('77',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('83',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['81','86'])).

thf('88',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('89',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['81','86'])).

thf('92',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('93',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('96',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('101',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['93','94','99','100'])).

thf('102',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['73','74'])).

thf('103',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['90','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['72','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EzV6Hw5TtS
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:49:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 487 iterations in 0.282s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.53/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(t70_xboole_1, conjecture,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.53/0.74            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.53/0.74       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.53/0.74            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.74        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.53/0.74               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.53/0.74          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.53/0.74               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 0.53/0.74  thf('0', plain,
% 0.53/0.74      ((~ (r1_xboole_0 @ sk_A @ sk_C)
% 0.53/0.74        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 0.53/0.74        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('1', plain,
% 0.53/0.74      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('split', [status(esa)], ['0'])).
% 0.53/0.74  thf('2', plain,
% 0.53/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.53/0.74        | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('3', plain,
% 0.53/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.53/0.74       ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.53/0.74      inference('split', [status(esa)], ['2'])).
% 0.53/0.74  thf('4', plain,
% 0.53/0.74      (~ ((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.53/0.74       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.53/0.74       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('split', [status(esa)], ['0'])).
% 0.53/0.74  thf('5', plain,
% 0.53/0.74      (((r1_xboole_0 @ sk_A @ sk_C)) <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('split', [status(esa)], ['2'])).
% 0.53/0.74  thf(d7_xboole_0, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.53/0.74       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.53/0.74  thf('6', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.53/0.74  thf('7', plain,
% 0.53/0.74      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.74  thf('8', plain,
% 0.53/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.53/0.74        | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('9', plain,
% 0.53/0.74      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('split', [status(esa)], ['8'])).
% 0.53/0.74  thf('10', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.53/0.74  thf('11', plain,
% 0.53/0.74      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.53/0.74  thf(t47_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.53/0.74  thf('12', plain,
% 0.53/0.74      (![X12 : $i, X13 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.53/0.74           = (k4_xboole_0 @ X12 @ X13))),
% 0.53/0.74      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.53/0.74  thf('13', plain,
% 0.53/0.74      ((((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['11', '12'])).
% 0.53/0.74  thf(t3_boole, axiom,
% 0.53/0.74    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.53/0.74  thf('14', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.53/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.53/0.74  thf('15', plain,
% 0.53/0.74      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_B)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('demod', [status(thm)], ['13', '14'])).
% 0.53/0.74  thf(t41_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.53/0.74       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.53/0.74  thf('16', plain,
% 0.53/0.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.53/0.74           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.74  thf('17', plain,
% 0.53/0.74      ((![X0 : $i]:
% 0.53/0.74          ((k4_xboole_0 @ sk_A @ X0)
% 0.53/0.74            = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['15', '16'])).
% 0.53/0.74  thf(t48_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      (![X14 : $i, X15 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.53/0.74           = (k3_xboole_0 @ X14 @ X15))),
% 0.53/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.74  thf('19', plain,
% 0.53/0.74      ((![X0 : $i]:
% 0.53/0.74          ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 0.53/0.74            = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['17', '18'])).
% 0.53/0.74  thf('20', plain,
% 0.53/0.74      (![X14 : $i, X15 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.53/0.74           = (k3_xboole_0 @ X14 @ X15))),
% 0.53/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.74  thf('21', plain,
% 0.53/0.74      ((![X0 : $i]:
% 0.53/0.74          ((k3_xboole_0 @ sk_A @ X0)
% 0.53/0.74            = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('demod', [status(thm)], ['19', '20'])).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      (![X0 : $i, X2 : $i]:
% 0.53/0.74         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.53/0.74  thf('23', plain,
% 0.53/0.74      ((![X0 : $i]:
% 0.53/0.74          (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 0.53/0.74           | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['21', '22'])).
% 0.53/0.74  thf('24', plain,
% 0.53/0.74      (((((k1_xboole_0) != (k1_xboole_0))
% 0.53/0.74         | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)) & ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['7', '23'])).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)) & ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['24'])).
% 0.53/0.74  thf('26', plain,
% 0.53/0.74      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.53/0.74         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.53/0.74      inference('split', [status(esa)], ['0'])).
% 0.53/0.74  thf('27', plain,
% 0.53/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.53/0.74       ~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('sup-', [status(thm)], ['25', '26'])).
% 0.53/0.74  thf('28', plain,
% 0.53/0.74      ((![X0 : $i]:
% 0.53/0.74          ((k4_xboole_0 @ sk_A @ X0)
% 0.53/0.74            = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['15', '16'])).
% 0.53/0.74  thf('29', plain,
% 0.53/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.53/0.74      inference('split', [status(esa)], ['8'])).
% 0.53/0.74  thf('30', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.53/0.74  thf('31', plain,
% 0.53/0.74      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.74  thf('32', plain,
% 0.53/0.74      (![X12 : $i, X13 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.53/0.74           = (k4_xboole_0 @ X12 @ X13))),
% 0.53/0.74      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.53/0.74  thf('33', plain,
% 0.53/0.74      ((((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.53/0.74          = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['31', '32'])).
% 0.53/0.74  thf('34', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.53/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.53/0.74  thf('35', plain,
% 0.53/0.74      ((((sk_A) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.53/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.53/0.74  thf('36', plain,
% 0.53/0.74      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_C)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.53/0.74             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['28', '35'])).
% 0.53/0.74  thf('37', plain,
% 0.53/0.74      (![X14 : $i, X15 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.53/0.74           = (k3_xboole_0 @ X14 @ X15))),
% 0.53/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.74  thf('38', plain,
% 0.53/0.74      ((((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.53/0.74             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['36', '37'])).
% 0.53/0.74  thf(idempotence_k2_xboole_0, axiom,
% 0.53/0.74    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.53/0.74  thf('39', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.53/0.74  thf(t46_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.53/0.74  thf('40', plain,
% 0.53/0.74      (![X10 : $i, X11 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.53/0.74  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['39', '40'])).
% 0.53/0.74  thf('42', plain,
% 0.53/0.74      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.53/0.74             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('demod', [status(thm)], ['38', '41'])).
% 0.53/0.74  thf('43', plain,
% 0.53/0.74      (![X0 : $i, X2 : $i]:
% 0.53/0.74         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.53/0.74  thf('44', plain,
% 0.53/0.74      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.53/0.74             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['42', '43'])).
% 0.53/0.74  thf('45', plain,
% 0.53/0.74      (((r1_xboole_0 @ sk_A @ sk_C))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.53/0.74             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['44'])).
% 0.53/0.74  thf('46', plain,
% 0.53/0.74      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('split', [status(esa)], ['0'])).
% 0.53/0.74  thf('47', plain,
% 0.53/0.74      (~ ((r1_xboole_0 @ sk_A @ sk_B)) | ((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.53/0.74       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['45', '46'])).
% 0.53/0.74  thf('48', plain,
% 0.53/0.74      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.53/0.74       ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('split', [status(esa)], ['8'])).
% 0.53/0.74  thf('49', plain,
% 0.53/0.74      ((((sk_A) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.53/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.53/0.74  thf('50', plain,
% 0.53/0.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.53/0.74           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.74  thf(t39_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.53/0.74  thf('51', plain,
% 0.53/0.74      (![X4 : $i, X5 : $i]:
% 0.53/0.74         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.53/0.74           = (k2_xboole_0 @ X4 @ X5))),
% 0.53/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.53/0.74  thf('52', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.53/0.74           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['50', '51'])).
% 0.53/0.74  thf('53', plain,
% 0.53/0.74      ((((k2_xboole_0 @ sk_C @ sk_A)
% 0.53/0.74          = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['49', '52'])).
% 0.53/0.74  thf('54', plain,
% 0.53/0.74      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.74  thf('55', plain,
% 0.53/0.74      (![X12 : $i, X13 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.53/0.74           = (k4_xboole_0 @ X12 @ X13))),
% 0.53/0.74      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.53/0.74  thf('56', plain,
% 0.53/0.74      ((((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['54', '55'])).
% 0.53/0.74  thf('57', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.53/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.53/0.74  thf('58', plain,
% 0.53/0.74      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_C)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('demod', [status(thm)], ['56', '57'])).
% 0.53/0.74  thf('59', plain,
% 0.53/0.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.53/0.74           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.74  thf('60', plain,
% 0.53/0.74      ((![X0 : $i]:
% 0.53/0.74          ((k4_xboole_0 @ sk_A @ X0)
% 0.53/0.74            = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0))))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['58', '59'])).
% 0.53/0.74  thf('61', plain,
% 0.53/0.74      ((((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.53/0.74          = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_A))))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.53/0.74             ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['53', '60'])).
% 0.53/0.74  thf('62', plain,
% 0.53/0.74      (![X14 : $i, X15 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.53/0.74           = (k3_xboole_0 @ X14 @ X15))),
% 0.53/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.74  thf('63', plain,
% 0.53/0.74      ((![X0 : $i]:
% 0.53/0.74          ((k4_xboole_0 @ sk_A @ X0)
% 0.53/0.74            = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0))))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['58', '59'])).
% 0.53/0.74  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['39', '40'])).
% 0.53/0.74  thf('65', plain,
% 0.53/0.74      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.53/0.74             ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.53/0.74  thf('66', plain,
% 0.53/0.74      (![X0 : $i, X2 : $i]:
% 0.53/0.74         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.53/0.74  thf('67', plain,
% 0.53/0.74      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B)))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.53/0.74             ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['65', '66'])).
% 0.53/0.74  thf('68', plain,
% 0.53/0.74      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.53/0.74             ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['67'])).
% 0.53/0.74  thf('69', plain,
% 0.53/0.74      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('split', [status(esa)], ['0'])).
% 0.53/0.74  thf('70', plain,
% 0.53/0.74      (~ ((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.53/0.74       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.53/0.74       ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('sup-', [status(thm)], ['68', '69'])).
% 0.53/0.74  thf('71', plain, (~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.53/0.74      inference('sat_resolution*', [status(thm)],
% 0.53/0.74                ['3', '4', '27', '47', '48', '70'])).
% 0.53/0.74  thf('72', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.53/0.74      inference('simpl_trail', [status(thm)], ['1', '71'])).
% 0.53/0.74  thf('73', plain,
% 0.53/0.74      ((((sk_A) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.53/0.74         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.53/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.53/0.74  thf('74', plain, (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.53/0.74      inference('sat_resolution*', [status(thm)], ['3', '4', '27', '47', '48'])).
% 0.53/0.74  thf('75', plain,
% 0.53/0.74      (((sk_A) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.53/0.74      inference('simpl_trail', [status(thm)], ['73', '74'])).
% 0.53/0.74  thf('76', plain,
% 0.53/0.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.53/0.74           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.74  thf('77', plain,
% 0.53/0.74      (![X14 : $i, X15 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.53/0.74           = (k3_xboole_0 @ X14 @ X15))),
% 0.53/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.74  thf('78', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X2 @ 
% 0.53/0.74           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 0.53/0.74           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['76', '77'])).
% 0.53/0.74  thf('79', plain,
% 0.53/0.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.53/0.74           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.74  thf('80', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X2 @ 
% 0.53/0.74           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 0.53/0.74           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['78', '79'])).
% 0.53/0.74  thf('81', plain,
% 0.53/0.74      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.53/0.74         = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.53/0.74      inference('sup+', [status(thm)], ['75', '80'])).
% 0.53/0.74  thf('82', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['39', '40'])).
% 0.53/0.74  thf('83', plain,
% 0.53/0.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.53/0.74           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.74  thf('84', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k1_xboole_0)
% 0.53/0.74           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['82', '83'])).
% 0.53/0.74  thf('85', plain,
% 0.53/0.74      (![X4 : $i, X5 : $i]:
% 0.53/0.74         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.53/0.74           = (k2_xboole_0 @ X4 @ X5))),
% 0.53/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.53/0.74  thf('86', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.53/0.74      inference('demod', [status(thm)], ['84', '85'])).
% 0.53/0.74  thf('87', plain,
% 0.53/0.74      (((k1_xboole_0) = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.53/0.74      inference('demod', [status(thm)], ['81', '86'])).
% 0.53/0.74  thf('88', plain,
% 0.53/0.74      (![X0 : $i, X2 : $i]:
% 0.53/0.74         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.53/0.74  thf('89', plain,
% 0.53/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.53/0.74        | (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.53/0.74      inference('sup-', [status(thm)], ['87', '88'])).
% 0.53/0.74  thf('90', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.53/0.74      inference('simplify', [status(thm)], ['89'])).
% 0.53/0.74  thf('91', plain,
% 0.53/0.74      (((k1_xboole_0) = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.53/0.74      inference('demod', [status(thm)], ['81', '86'])).
% 0.53/0.74  thf('92', plain,
% 0.53/0.74      (![X12 : $i, X13 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.53/0.74           = (k4_xboole_0 @ X12 @ X13))),
% 0.53/0.74      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.53/0.74  thf('93', plain,
% 0.53/0.74      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.53/0.74         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.53/0.74      inference('sup+', [status(thm)], ['91', '92'])).
% 0.53/0.74  thf('94', plain,
% 0.53/0.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.53/0.74           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.74  thf('95', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['39', '40'])).
% 0.53/0.74  thf('96', plain,
% 0.53/0.74      (![X4 : $i, X5 : $i]:
% 0.53/0.74         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.53/0.74           = (k2_xboole_0 @ X4 @ X5))),
% 0.53/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.53/0.74  thf('97', plain,
% 0.53/0.74      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['95', '96'])).
% 0.53/0.74  thf('98', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.53/0.74  thf('99', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['97', '98'])).
% 0.53/0.74  thf('100', plain,
% 0.53/0.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.53/0.74           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.74  thf('101', plain,
% 0.53/0.74      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.53/0.74         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.53/0.74      inference('demod', [status(thm)], ['93', '94', '99', '100'])).
% 0.53/0.74  thf('102', plain,
% 0.53/0.74      (((sk_A) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.53/0.74      inference('simpl_trail', [status(thm)], ['73', '74'])).
% 0.53/0.74  thf('103', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('sup+', [status(thm)], ['101', '102'])).
% 0.53/0.74  thf('104', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.53/0.74      inference('demod', [status(thm)], ['90', '103'])).
% 0.53/0.74  thf('105', plain, ($false), inference('demod', [status(thm)], ['72', '104'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
