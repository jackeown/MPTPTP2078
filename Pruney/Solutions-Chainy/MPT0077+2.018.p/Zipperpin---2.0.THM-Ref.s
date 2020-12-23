%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lt1Ji9mwwt

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:51 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 402 expanded)
%              Number of leaves         :   17 ( 132 expanded)
%              Depth                    :   17
%              Number of atoms          : 1031 (3432 expanded)
%              Number of equality atoms :   91 ( 334 expanded)
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
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('10',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['12','19'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
        = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ X0 )
        = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( ( r1_xboole_0 @ sk_A @ sk_B )
      & ( r1_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','28'])).

thf('30',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_A @ sk_B )
      & ( r1_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('35',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['7'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('39',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('41',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('46',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['42','53'])).

thf('55',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf('56',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('60',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('62',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('65',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('68',plain,
    ( ( ( k2_xboole_0 @ sk_C @ sk_A )
      = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('70',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('71',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('73',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
        = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ X0 )
        = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_A ) ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['68','77'])).

thf('79',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('80',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ X0 )
        = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('86',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('89',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['78','83','84','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('92',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['90','98'])).

thf('100',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('101',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','32','33','65','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lt1Ji9mwwt
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:06:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.39/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.60  % Solved by: fo/fo7.sh
% 0.39/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.60  % done 230 iterations in 0.136s
% 0.39/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.60  % SZS output start Refutation
% 0.39/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(t70_xboole_1, conjecture,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.39/0.60            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.39/0.60       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.39/0.60            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.60        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.39/0.60               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.39/0.60          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.39/0.60               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 0.39/0.60    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 0.39/0.60  thf('0', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.39/0.60        | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('1', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.39/0.60       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.39/0.60      inference('split', [status(esa)], ['0'])).
% 0.39/0.60  thf('2', plain,
% 0.39/0.60      ((~ (r1_xboole_0 @ sk_A @ sk_C)
% 0.39/0.60        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 0.39/0.60        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('3', plain,
% 0.39/0.60      (~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.39/0.60       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.39/0.60      inference('split', [status(esa)], ['2'])).
% 0.39/0.60  thf('4', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_A @ sk_C)) <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.60      inference('split', [status(esa)], ['0'])).
% 0.39/0.60  thf(d7_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.39/0.60       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.60  thf('5', plain,
% 0.39/0.60      (![X2 : $i, X3 : $i]:
% 0.39/0.60         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.60  thf('6', plain,
% 0.39/0.60      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.60  thf('7', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.39/0.60        | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('8', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('split', [status(esa)], ['7'])).
% 0.39/0.60  thf('9', plain,
% 0.39/0.60      (![X2 : $i, X3 : $i]:
% 0.39/0.60         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.60  thf('10', plain,
% 0.39/0.60      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.60  thf(t47_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.60  thf('11', plain,
% 0.39/0.60      (![X12 : $i, X13 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.39/0.60           = (k4_xboole_0 @ X12 @ X13))),
% 0.39/0.60      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.39/0.60  thf('12', plain,
% 0.39/0.60      ((((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.39/0.60  thf(t39_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.60  thf('13', plain,
% 0.39/0.60      (![X7 : $i, X8 : $i]:
% 0.39/0.60         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.39/0.60           = (k2_xboole_0 @ X7 @ X8))),
% 0.39/0.60      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.60  thf(commutativity_k2_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.39/0.60  thf('14', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.60  thf(t1_boole, axiom,
% 0.39/0.60    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.60  thf('15', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.39/0.60      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.60  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.60  thf('17', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['13', '16'])).
% 0.39/0.60  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.60  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.60  thf('20', plain,
% 0.39/0.60      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_B)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('demod', [status(thm)], ['12', '19'])).
% 0.39/0.60  thf(t41_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.60       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.60  thf('21', plain,
% 0.39/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.39/0.60           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.60  thf(t48_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.60  thf('22', plain,
% 0.39/0.60      (![X14 : $i, X15 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.39/0.60           = (k3_xboole_0 @ X14 @ X15))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('23', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.39/0.60           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['21', '22'])).
% 0.39/0.60  thf('24', plain,
% 0.39/0.60      ((![X0 : $i]:
% 0.39/0.60          ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 0.39/0.60            = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['20', '23'])).
% 0.39/0.60  thf('25', plain,
% 0.39/0.60      (![X14 : $i, X15 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.39/0.60           = (k3_xboole_0 @ X14 @ X15))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('26', plain,
% 0.39/0.60      ((![X0 : $i]:
% 0.39/0.60          ((k3_xboole_0 @ sk_A @ X0)
% 0.39/0.60            = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.39/0.60  thf('27', plain,
% 0.39/0.60      (![X2 : $i, X4 : $i]:
% 0.39/0.60         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.60  thf('28', plain,
% 0.39/0.60      ((![X0 : $i]:
% 0.39/0.60          (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 0.39/0.60           | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.60  thf('29', plain,
% 0.39/0.60      (((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.60         | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_B)) & ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['6', '28'])).
% 0.39/0.60  thf('30', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_B)) & ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.60      inference('simplify', [status(thm)], ['29'])).
% 0.39/0.60  thf('31', plain,
% 0.39/0.60      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.39/0.60         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('split', [status(esa)], ['2'])).
% 0.39/0.60  thf('32', plain,
% 0.39/0.60      (~ ((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.39/0.60       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.39/0.60       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.60  thf('33', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.39/0.60       ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.60      inference('split', [status(esa)], ['7'])).
% 0.39/0.60  thf('34', plain,
% 0.39/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.39/0.60           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.60  thf('35', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('split', [status(esa)], ['7'])).
% 0.39/0.60  thf('36', plain,
% 0.39/0.60      (![X2 : $i, X3 : $i]:
% 0.39/0.60         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.60  thf('37', plain,
% 0.39/0.60      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.60  thf('38', plain,
% 0.39/0.60      (![X12 : $i, X13 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.39/0.60           = (k4_xboole_0 @ X12 @ X13))),
% 0.39/0.60      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.39/0.60  thf('39', plain,
% 0.39/0.60      ((((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.39/0.60          = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['37', '38'])).
% 0.39/0.60  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.60  thf('41', plain,
% 0.39/0.60      ((((sk_A) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.60  thf('42', plain,
% 0.39/0.60      ((((sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['34', '41'])).
% 0.39/0.60  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.60  thf('44', plain,
% 0.39/0.60      (![X14 : $i, X15 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.39/0.60           = (k3_xboole_0 @ X14 @ X15))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('45', plain,
% 0.39/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['43', '44'])).
% 0.39/0.60  thf(t2_boole, axiom,
% 0.39/0.60    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.60  thf('46', plain,
% 0.39/0.60      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('cnf', [status(esa)], [t2_boole])).
% 0.39/0.60  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['45', '46'])).
% 0.39/0.60  thf('48', plain,
% 0.39/0.60      (![X7 : $i, X8 : $i]:
% 0.39/0.60         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.39/0.60           = (k2_xboole_0 @ X7 @ X8))),
% 0.39/0.60      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.60  thf('49', plain,
% 0.39/0.60      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['47', '48'])).
% 0.39/0.60  thf('50', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.39/0.60      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.60  thf('51', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.39/0.60      inference('demod', [status(thm)], ['49', '50'])).
% 0.39/0.60  thf('52', plain,
% 0.39/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.39/0.60           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.60  thf('53', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.39/0.60           = (k4_xboole_0 @ X1 @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['51', '52'])).
% 0.39/0.60  thf('54', plain,
% 0.39/0.60      ((((k4_xboole_0 @ sk_A @ sk_C)
% 0.39/0.60          = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['42', '53'])).
% 0.39/0.60  thf('55', plain,
% 0.39/0.60      ((((sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['34', '41'])).
% 0.39/0.60  thf('56', plain,
% 0.39/0.60      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_C)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['54', '55'])).
% 0.39/0.60  thf('57', plain,
% 0.39/0.60      (![X14 : $i, X15 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.39/0.60           = (k3_xboole_0 @ X14 @ X15))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('58', plain,
% 0.39/0.60      ((((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['56', '57'])).
% 0.39/0.60  thf('59', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['45', '46'])).
% 0.39/0.60  thf('60', plain,
% 0.39/0.60      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('demod', [status(thm)], ['58', '59'])).
% 0.39/0.60  thf('61', plain,
% 0.39/0.60      (![X2 : $i, X4 : $i]:
% 0.39/0.60         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.60  thf('62', plain,
% 0.39/0.60      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.39/0.60  thf('63', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_A @ sk_C))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('simplify', [status(thm)], ['62'])).
% 0.39/0.60  thf('64', plain,
% 0.39/0.60      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.60      inference('split', [status(esa)], ['2'])).
% 0.39/0.60  thf('65', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.39/0.60       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['63', '64'])).
% 0.39/0.60  thf('66', plain,
% 0.39/0.60      ((((sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['34', '41'])).
% 0.39/0.60  thf('67', plain,
% 0.39/0.60      (![X7 : $i, X8 : $i]:
% 0.39/0.60         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.39/0.60           = (k2_xboole_0 @ X7 @ X8))),
% 0.39/0.60      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.60  thf('68', plain,
% 0.39/0.60      ((((k2_xboole_0 @ sk_C @ sk_A)
% 0.39/0.60          = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['66', '67'])).
% 0.39/0.60  thf('69', plain,
% 0.39/0.60      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.60  thf('70', plain,
% 0.39/0.60      (![X12 : $i, X13 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.39/0.60           = (k4_xboole_0 @ X12 @ X13))),
% 0.39/0.60      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.39/0.60  thf('71', plain,
% 0.39/0.60      ((((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['69', '70'])).
% 0.39/0.60  thf('72', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.60  thf('73', plain,
% 0.39/0.60      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_C)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.60      inference('demod', [status(thm)], ['71', '72'])).
% 0.39/0.60  thf('74', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.39/0.60           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['21', '22'])).
% 0.39/0.60  thf('75', plain,
% 0.39/0.60      ((![X0 : $i]:
% 0.39/0.60          ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 0.39/0.60            = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0))))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['73', '74'])).
% 0.39/0.60  thf('76', plain,
% 0.39/0.60      (![X14 : $i, X15 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.39/0.60           = (k3_xboole_0 @ X14 @ X15))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('77', plain,
% 0.39/0.60      ((![X0 : $i]:
% 0.39/0.60          ((k3_xboole_0 @ sk_A @ X0)
% 0.39/0.60            = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0))))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.60      inference('demod', [status(thm)], ['75', '76'])).
% 0.39/0.60  thf('78', plain,
% 0.39/0.60      ((((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.39/0.60          = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_A))))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.39/0.60             ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['68', '77'])).
% 0.39/0.60  thf('79', plain,
% 0.39/0.60      (![X14 : $i, X15 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.39/0.60           = (k3_xboole_0 @ X14 @ X15))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('80', plain,
% 0.39/0.60      (![X14 : $i, X15 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.39/0.60           = (k3_xboole_0 @ X14 @ X15))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('81', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.60           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['79', '80'])).
% 0.39/0.60  thf('82', plain,
% 0.39/0.60      (![X12 : $i, X13 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.39/0.60           = (k4_xboole_0 @ X12 @ X13))),
% 0.39/0.60      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.39/0.60  thf('83', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.39/0.60           = (k4_xboole_0 @ X1 @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['81', '82'])).
% 0.39/0.60  thf('84', plain,
% 0.39/0.60      ((![X0 : $i]:
% 0.39/0.60          ((k3_xboole_0 @ sk_A @ X0)
% 0.39/0.60            = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0))))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.60      inference('demod', [status(thm)], ['75', '76'])).
% 0.39/0.60  thf('85', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['45', '46'])).
% 0.39/0.60  thf('86', plain,
% 0.39/0.60      (![X14 : $i, X15 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.39/0.60           = (k3_xboole_0 @ X14 @ X15))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('87', plain,
% 0.39/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['85', '86'])).
% 0.39/0.60  thf('88', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.60  thf('89', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.39/0.60      inference('demod', [status(thm)], ['87', '88'])).
% 0.39/0.60  thf('90', plain,
% 0.39/0.60      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.39/0.60             ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.60      inference('demod', [status(thm)], ['78', '83', '84', '89'])).
% 0.39/0.60  thf('91', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.39/0.60           = (k4_xboole_0 @ X1 @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['51', '52'])).
% 0.39/0.60  thf('92', plain,
% 0.39/0.60      (![X14 : $i, X15 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.39/0.60           = (k3_xboole_0 @ X14 @ X15))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('93', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.39/0.60           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['91', '92'])).
% 0.39/0.60  thf('94', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['45', '46'])).
% 0.39/0.60  thf('95', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k1_xboole_0) = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.39/0.60      inference('demod', [status(thm)], ['93', '94'])).
% 0.39/0.60  thf('96', plain,
% 0.39/0.60      (![X2 : $i, X4 : $i]:
% 0.39/0.60         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.60  thf('97', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.60          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['95', '96'])).
% 0.39/0.60  thf('98', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.39/0.60      inference('simplify', [status(thm)], ['97'])).
% 0.39/0.60  thf('99', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.39/0.60             ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['90', '98'])).
% 0.39/0.60  thf('100', plain,
% 0.39/0.60      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('split', [status(esa)], ['2'])).
% 0.39/0.60  thf('101', plain,
% 0.39/0.60      (~ ((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.39/0.60       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.39/0.60       ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['99', '100'])).
% 0.39/0.60  thf('102', plain, ($false),
% 0.39/0.60      inference('sat_resolution*', [status(thm)],
% 0.39/0.60                ['1', '3', '32', '33', '65', '101'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
