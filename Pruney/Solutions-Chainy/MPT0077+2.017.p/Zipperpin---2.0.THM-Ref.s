%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QPE5Kfi77b

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:51 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 305 expanded)
%              Number of leaves         :   17 (  95 expanded)
%              Depth                    :   18
%              Number of atoms          :  987 (3126 expanded)
%              Number of equality atoms :   82 ( 200 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
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
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
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
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
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
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
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
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
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
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
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

thf('39',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('42',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','4','27','49'])).

thf('51',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('52',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('61',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('64',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('74',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','75'])).

thf('77',plain,
    ( ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','76'])).

thf('78',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('79',plain,
    ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('82',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('83',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('86',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80','81','84','85'])).

thf('87',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('88',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('90',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('91',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('93',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['3','4','27','49','92'])).

thf('94',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['91','93'])).

thf('95',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('96',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['51','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QPE5Kfi77b
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 345 iterations in 0.171s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.43/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(t70_xboole_1, conjecture,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.43/0.62            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.43/0.62       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.43/0.62            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.62        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.43/0.62               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.43/0.62          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.43/0.62               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      ((~ (r1_xboole_0 @ sk_A @ sk_C)
% 0.43/0.62        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 0.43/0.62        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.43/0.62        | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.43/0.62       ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.43/0.62      inference('split', [status(esa)], ['2'])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (~ ((r1_xboole_0 @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.43/0.62       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_A @ sk_C)) <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.43/0.62      inference('split', [status(esa)], ['2'])).
% 0.43/0.62  thf(d7_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.43/0.62       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.43/0.62        | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['8'])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.43/0.62  thf(t47_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X12 : $i, X13 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.43/0.62           = (k4_xboole_0 @ X12 @ X13))),
% 0.43/0.62      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      ((((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.43/0.62  thf(t3_boole, axiom,
% 0.43/0.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.62  thf('14', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_B)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.43/0.62  thf(t41_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.43/0.62       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.43/0.62           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          ((k4_xboole_0 @ sk_A @ X0)
% 0.43/0.62            = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.43/0.62  thf(t48_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.43/0.62           = (k3_xboole_0 @ X14 @ X15))),
% 0.43/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 0.43/0.62            = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['17', '18'])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.43/0.62           = (k3_xboole_0 @ X14 @ X15))),
% 0.43/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          ((k3_xboole_0 @ sk_A @ X0)
% 0.43/0.62            = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['19', '20'])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (![X2 : $i, X4 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 0.43/0.62           | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (((((k1_xboole_0) != (k1_xboole_0))
% 0.43/0.62         | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ sk_B)) & ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['7', '23'])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ sk_B)) & ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.43/0.62         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.43/0.62       ~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          ((k4_xboole_0 @ sk_A @ X0)
% 0.43/0.62            = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.43/0.62      inference('split', [status(esa)], ['8'])).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (![X12 : $i, X13 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.43/0.62           = (k4_xboole_0 @ X12 @ X13))),
% 0.43/0.62      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      ((((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.43/0.62          = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.43/0.62  thf('34', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.62  thf('35', plain,
% 0.43/0.62      ((((sk_A) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.43/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_C)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.43/0.62             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['28', '35'])).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.43/0.62           = (k3_xboole_0 @ X14 @ X15))),
% 0.43/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.62  thf('38', plain,
% 0.43/0.62      ((((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.43/0.62             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['36', '37'])).
% 0.43/0.62  thf('39', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.43/0.62           = (k3_xboole_0 @ X14 @ X15))),
% 0.43/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['39', '40'])).
% 0.43/0.62  thf(t2_boole, axiom,
% 0.43/0.62    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.43/0.62  thf('42', plain,
% 0.43/0.62      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t2_boole])).
% 0.43/0.62  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.43/0.62             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['38', '43'])).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      (![X2 : $i, X4 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.43/0.62             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['44', '45'])).
% 0.43/0.62  thf('47', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_A @ sk_C))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.43/0.62             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['46'])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('49', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.43/0.62       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.43/0.62       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.43/0.62  thf('50', plain, (~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['3', '4', '27', '49'])).
% 0.43/0.62  thf('51', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 0.43/0.62  thf('52', plain,
% 0.43/0.62      ((((sk_A) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.43/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.43/0.62           = (k3_xboole_0 @ X14 @ X15))),
% 0.43/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.62  thf('54', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.43/0.62           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.62  thf('55', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.43/0.62           = (k4_xboole_0 @ X2 @ 
% 0.43/0.62              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['53', '54'])).
% 0.43/0.62  thf('56', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.43/0.62           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.62  thf('57', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.43/0.62           = (k4_xboole_0 @ X2 @ 
% 0.43/0.62              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.43/0.62      inference('demod', [status(thm)], ['55', '56'])).
% 0.43/0.62  thf('58', plain,
% 0.43/0.62      ((((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.43/0.62          = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A))))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['52', '57'])).
% 0.43/0.62  thf(commutativity_k2_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.43/0.62  thf('59', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.62  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf('61', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.43/0.62           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.62  thf('62', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.43/0.62           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['60', '61'])).
% 0.43/0.62  thf('63', plain,
% 0.43/0.62      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t2_boole])).
% 0.43/0.62  thf('64', plain,
% 0.43/0.62      (![X2 : $i, X4 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.62  thf('65', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['63', '64'])).
% 0.43/0.62  thf('66', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.43/0.62      inference('simplify', [status(thm)], ['65'])).
% 0.43/0.62  thf(symmetry_r1_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.43/0.62  thf('67', plain,
% 0.43/0.62      (![X5 : $i, X6 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.43/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.43/0.62  thf('68', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.43/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.43/0.62  thf('69', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.62  thf('70', plain,
% 0.43/0.62      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.43/0.62  thf('71', plain,
% 0.43/0.62      (![X12 : $i, X13 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.43/0.62           = (k4_xboole_0 @ X12 @ X13))),
% 0.43/0.62      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.43/0.62  thf('72', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.43/0.62           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['70', '71'])).
% 0.43/0.62  thf('73', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.62  thf('74', plain,
% 0.43/0.62      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['72', '73'])).
% 0.43/0.62  thf('75', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['62', '74'])).
% 0.43/0.62  thf('76', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['59', '75'])).
% 0.43/0.62  thf('77', plain,
% 0.43/0.62      ((((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.43/0.62      inference('demod', [status(thm)], ['58', '76'])).
% 0.43/0.62  thf('78', plain,
% 0.43/0.62      (![X12 : $i, X13 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.43/0.62           = (k4_xboole_0 @ X12 @ X13))),
% 0.43/0.62      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.43/0.62  thf('79', plain,
% 0.43/0.62      ((((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.43/0.62          = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['77', '78'])).
% 0.43/0.62  thf('80', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.43/0.62           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.62  thf('81', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.62  thf('82', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.62  thf('83', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.43/0.62           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.62  thf('84', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X0 @ X1)
% 0.43/0.62           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['82', '83'])).
% 0.43/0.62  thf('85', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.43/0.62           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.43/0.62  thf('86', plain,
% 0.43/0.62      ((((k4_xboole_0 @ sk_A @ sk_B)
% 0.43/0.62          = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.43/0.62      inference('demod', [status(thm)], ['79', '80', '81', '84', '85'])).
% 0.43/0.62  thf('87', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.43/0.62           = (k3_xboole_0 @ X14 @ X15))),
% 0.43/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.62  thf('88', plain,
% 0.43/0.62      ((((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.43/0.62          = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['86', '87'])).
% 0.43/0.62  thf('89', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.43/0.62           = (k3_xboole_0 @ X14 @ X15))),
% 0.43/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.62  thf('90', plain,
% 0.43/0.62      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.43/0.62  thf('91', plain,
% 0.43/0.62      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.43/0.62         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.43/0.62      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.43/0.62  thf('92', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.43/0.62       ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.62      inference('split', [status(esa)], ['8'])).
% 0.43/0.62  thf('93', plain, (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['3', '4', '27', '49', '92'])).
% 0.43/0.62  thf('94', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['91', '93'])).
% 0.43/0.62  thf('95', plain,
% 0.43/0.62      (![X2 : $i, X4 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.62  thf('96', plain,
% 0.43/0.62      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['94', '95'])).
% 0.43/0.62  thf('97', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.43/0.62      inference('simplify', [status(thm)], ['96'])).
% 0.43/0.62  thf('98', plain, ($false), inference('demod', [status(thm)], ['51', '97'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
