%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gvvNCN2PTq

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:49 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 913 expanded)
%              Number of leaves         :   17 ( 300 expanded)
%              Depth                    :   24
%              Number of atoms          : 1160 (7761 expanded)
%              Number of equality atoms :  105 ( 731 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

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

thf('6',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','11','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('29',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','32','33'])).

thf('35',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','39'])).

thf('41',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['15','40'])).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('43',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('52',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','11','14'])).

thf('53',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','39'])).

thf('55',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('57',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('59',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['2','50','62'])).

thf('64',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('70',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['67','74'])).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('79',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('84',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('86',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('88',plain,
    ( ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('90',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_C
      = ( k4_xboole_0 @ sk_C @ sk_A ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['80','90'])).

thf('92',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['81'])).

thf('93',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','50','62','92'])).

thf('94',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['91','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','32','33'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['94','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('104',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('105',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('106',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('108',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('110',plain,
    ( ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('112',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ sk_A ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['103','112'])).

thf('114',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('115',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','50','62','114'])).

thf('116',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['113','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('118',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['118','121'])).

thf('123',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup+',[status(thm)],['102','122'])).

thf('124',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('125',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('127',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('129',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['64','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gvvNCN2PTq
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 2.13/2.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.13/2.38  % Solved by: fo/fo7.sh
% 2.13/2.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.13/2.38  % done 2304 iterations in 1.926s
% 2.13/2.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.13/2.38  % SZS output start Refutation
% 2.13/2.38  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.13/2.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.13/2.38  thf(sk_C_type, type, sk_C: $i).
% 2.13/2.38  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.13/2.38  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.13/2.38  thf(sk_A_type, type, sk_A: $i).
% 2.13/2.38  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.13/2.38  thf(sk_B_type, type, sk_B: $i).
% 2.13/2.38  thf(t70_xboole_1, conjecture,
% 2.13/2.38    (![A:$i,B:$i,C:$i]:
% 2.13/2.38     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.13/2.38            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.13/2.38       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.13/2.38            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.13/2.38  thf(zf_stmt_0, negated_conjecture,
% 2.13/2.38    (~( ![A:$i,B:$i,C:$i]:
% 2.13/2.38        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.13/2.38               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.13/2.38          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.13/2.38               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 2.13/2.38    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 2.13/2.38  thf('0', plain,
% 2.13/2.38      ((~ (r1_xboole_0 @ sk_A @ sk_C)
% 2.13/2.38        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 2.13/2.38        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.13/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.38  thf('1', plain,
% 2.13/2.38      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 2.13/2.38         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('split', [status(esa)], ['0'])).
% 2.13/2.38  thf('2', plain,
% 2.13/2.38      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 2.13/2.38       ~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 2.13/2.38      inference('split', [status(esa)], ['0'])).
% 2.13/2.38  thf('3', plain,
% 2.13/2.38      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 2.13/2.38        | (r1_xboole_0 @ sk_A @ sk_B))),
% 2.13/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.38  thf('4', plain,
% 2.13/2.38      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('split', [status(esa)], ['3'])).
% 2.13/2.38  thf(d7_xboole_0, axiom,
% 2.13/2.38    (![A:$i,B:$i]:
% 2.13/2.38     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.13/2.38       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.13/2.38  thf('5', plain,
% 2.13/2.38      (![X4 : $i, X5 : $i]:
% 2.13/2.38         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 2.13/2.38      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.13/2.38  thf('6', plain,
% 2.13/2.38      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('sup-', [status(thm)], ['4', '5'])).
% 2.13/2.38  thf(t48_xboole_1, axiom,
% 2.13/2.38    (![A:$i,B:$i]:
% 2.13/2.38     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.13/2.38  thf('7', plain,
% 2.13/2.38      (![X12 : $i, X13 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 2.13/2.38           = (k3_xboole_0 @ X12 @ X13))),
% 2.13/2.38      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.13/2.38  thf('8', plain,
% 2.13/2.38      (![X12 : $i, X13 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 2.13/2.38           = (k3_xboole_0 @ X12 @ X13))),
% 2.13/2.38      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.13/2.38  thf('9', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.13/2.38           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('sup+', [status(thm)], ['7', '8'])).
% 2.13/2.38  thf('10', plain,
% 2.13/2.38      ((((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 2.13/2.38          = (k3_xboole_0 @ sk_A @ 
% 2.13/2.38             (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('sup+', [status(thm)], ['6', '9'])).
% 2.13/2.38  thf(t3_boole, axiom,
% 2.13/2.38    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.13/2.38  thf('11', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 2.13/2.38      inference('cnf', [status(esa)], [t3_boole])).
% 2.13/2.38  thf(commutativity_k2_xboole_0, axiom,
% 2.13/2.38    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.13/2.38  thf('12', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.13/2.38      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.13/2.38  thf(t41_xboole_1, axiom,
% 2.13/2.38    (![A:$i,B:$i,C:$i]:
% 2.13/2.38     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.13/2.38       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.13/2.38  thf('13', plain,
% 2.13/2.38      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 2.13/2.38           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.13/2.38      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.13/2.38  thf('14', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 2.13/2.38           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('sup+', [status(thm)], ['12', '13'])).
% 2.13/2.38  thf('15', plain,
% 2.13/2.38      ((((sk_A)
% 2.13/2.38          = (k3_xboole_0 @ sk_A @ 
% 2.13/2.38             (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('demod', [status(thm)], ['10', '11', '14'])).
% 2.13/2.38  thf(commutativity_k3_xboole_0, axiom,
% 2.13/2.38    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.13/2.38  thf('16', plain,
% 2.13/2.38      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.13/2.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.13/2.38  thf('17', plain,
% 2.13/2.38      (![X12 : $i, X13 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 2.13/2.38           = (k3_xboole_0 @ X12 @ X13))),
% 2.13/2.38      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.13/2.38  thf('18', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 2.13/2.38           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('sup+', [status(thm)], ['12', '13'])).
% 2.13/2.38  thf('19', plain,
% 2.13/2.38      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 2.13/2.38           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.13/2.38      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.13/2.38  thf('20', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 2.13/2.38           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 2.13/2.38      inference('sup+', [status(thm)], ['18', '19'])).
% 2.13/2.38  thf(idempotence_k2_xboole_0, axiom,
% 2.13/2.38    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 2.13/2.38  thf('21', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 2.13/2.38      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.13/2.38  thf('22', plain,
% 2.13/2.38      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 2.13/2.38           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.13/2.38      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.13/2.38  thf('23', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 2.13/2.38           = (k4_xboole_0 @ X1 @ X0))),
% 2.13/2.38      inference('sup+', [status(thm)], ['21', '22'])).
% 2.13/2.38  thf('24', plain,
% 2.13/2.38      (![X12 : $i, X13 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 2.13/2.38           = (k3_xboole_0 @ X12 @ X13))),
% 2.13/2.38      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.13/2.38  thf('25', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.13/2.38           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 2.13/2.38      inference('sup+', [status(thm)], ['23', '24'])).
% 2.13/2.38  thf('26', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 2.13/2.38      inference('cnf', [status(esa)], [t3_boole])).
% 2.13/2.38  thf('27', plain,
% 2.13/2.38      (![X12 : $i, X13 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 2.13/2.38           = (k3_xboole_0 @ X12 @ X13))),
% 2.13/2.38      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.13/2.38  thf('28', plain,
% 2.13/2.38      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.13/2.38      inference('sup+', [status(thm)], ['26', '27'])).
% 2.13/2.38  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 2.13/2.38  thf('29', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 2.13/2.38      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.13/2.38  thf('30', plain,
% 2.13/2.38      (![X4 : $i, X5 : $i]:
% 2.13/2.38         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 2.13/2.38      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.13/2.38  thf('31', plain,
% 2.13/2.38      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.13/2.38      inference('sup-', [status(thm)], ['29', '30'])).
% 2.13/2.38  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.13/2.38      inference('demod', [status(thm)], ['28', '31'])).
% 2.13/2.38  thf('33', plain,
% 2.13/2.38      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.13/2.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.13/2.38  thf('34', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('demod', [status(thm)], ['25', '32', '33'])).
% 2.13/2.38  thf('35', plain,
% 2.13/2.38      (![X4 : $i, X6 : $i]:
% 2.13/2.38         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 2.13/2.38      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.13/2.38  thf('36', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         (((k1_xboole_0) != (k1_xboole_0))
% 2.13/2.38          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('sup-', [status(thm)], ['34', '35'])).
% 2.13/2.38  thf('37', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.13/2.38      inference('simplify', [status(thm)], ['36'])).
% 2.13/2.38  thf('38', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.38         (r1_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 2.13/2.38      inference('sup+', [status(thm)], ['20', '37'])).
% 2.13/2.38  thf('39', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.38         (r1_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 2.13/2.38      inference('sup+', [status(thm)], ['17', '38'])).
% 2.13/2.38  thf('40', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.38         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('sup+', [status(thm)], ['16', '39'])).
% 2.13/2.38  thf('41', plain,
% 2.13/2.38      (((r1_xboole_0 @ sk_B @ sk_A))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('sup+', [status(thm)], ['15', '40'])).
% 2.13/2.38  thf('42', plain,
% 2.13/2.38      (![X4 : $i, X5 : $i]:
% 2.13/2.38         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 2.13/2.38      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.13/2.38  thf('43', plain,
% 2.13/2.38      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('sup-', [status(thm)], ['41', '42'])).
% 2.13/2.38  thf('44', plain,
% 2.13/2.38      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.13/2.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.13/2.38  thf('45', plain,
% 2.13/2.38      (![X4 : $i, X6 : $i]:
% 2.13/2.38         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 2.13/2.38      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.13/2.38  thf('46', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 2.13/2.38      inference('sup-', [status(thm)], ['44', '45'])).
% 2.13/2.38  thf('47', plain,
% 2.13/2.38      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B)))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('sup-', [status(thm)], ['43', '46'])).
% 2.13/2.38  thf('48', plain,
% 2.13/2.38      (((r1_xboole_0 @ sk_A @ sk_B))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('simplify', [status(thm)], ['47'])).
% 2.13/2.38  thf('49', plain,
% 2.13/2.38      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 2.13/2.38      inference('split', [status(esa)], ['0'])).
% 2.13/2.38  thf('50', plain,
% 2.13/2.38      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 2.13/2.38       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.13/2.38      inference('sup-', [status(thm)], ['48', '49'])).
% 2.13/2.38  thf('51', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 2.13/2.38           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 2.13/2.38      inference('sup+', [status(thm)], ['18', '19'])).
% 2.13/2.38  thf('52', plain,
% 2.13/2.38      ((((sk_A)
% 2.13/2.38          = (k3_xboole_0 @ sk_A @ 
% 2.13/2.38             (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('demod', [status(thm)], ['10', '11', '14'])).
% 2.13/2.38  thf('53', plain,
% 2.13/2.38      ((((sk_A)
% 2.13/2.38          = (k3_xboole_0 @ sk_A @ 
% 2.13/2.38             (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('sup+', [status(thm)], ['51', '52'])).
% 2.13/2.38  thf('54', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.38         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('sup+', [status(thm)], ['16', '39'])).
% 2.13/2.38  thf('55', plain,
% 2.13/2.38      (((r1_xboole_0 @ sk_C @ sk_A))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('sup+', [status(thm)], ['53', '54'])).
% 2.13/2.38  thf('56', plain,
% 2.13/2.38      (![X4 : $i, X5 : $i]:
% 2.13/2.38         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 2.13/2.38      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.13/2.38  thf('57', plain,
% 2.13/2.38      ((((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0)))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('sup-', [status(thm)], ['55', '56'])).
% 2.13/2.38  thf('58', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 2.13/2.38      inference('sup-', [status(thm)], ['44', '45'])).
% 2.13/2.38  thf('59', plain,
% 2.13/2.38      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C)))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('sup-', [status(thm)], ['57', '58'])).
% 2.13/2.38  thf('60', plain,
% 2.13/2.38      (((r1_xboole_0 @ sk_A @ sk_C))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.13/2.38      inference('simplify', [status(thm)], ['59'])).
% 2.13/2.38  thf('61', plain,
% 2.13/2.38      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 2.13/2.38      inference('split', [status(esa)], ['0'])).
% 2.13/2.38  thf('62', plain,
% 2.13/2.38      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 2.13/2.38       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.13/2.38      inference('sup-', [status(thm)], ['60', '61'])).
% 2.13/2.38  thf('63', plain, (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.13/2.38      inference('sat_resolution*', [status(thm)], ['2', '50', '62'])).
% 2.13/2.38  thf('64', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 2.13/2.38      inference('simpl_trail', [status(thm)], ['1', '63'])).
% 2.13/2.38  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.13/2.38      inference('demod', [status(thm)], ['28', '31'])).
% 2.13/2.38  thf('66', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 2.13/2.38           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 2.13/2.38      inference('sup+', [status(thm)], ['18', '19'])).
% 2.13/2.38  thf('67', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ k1_xboole_0 @ X1)
% 2.13/2.38           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 2.13/2.38      inference('sup+', [status(thm)], ['65', '66'])).
% 2.13/2.38  thf('68', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 2.13/2.38      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.13/2.38  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.13/2.38      inference('demod', [status(thm)], ['28', '31'])).
% 2.13/2.38  thf('70', plain,
% 2.13/2.38      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 2.13/2.38           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.13/2.38      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.13/2.38  thf('71', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 2.13/2.38           = (k1_xboole_0))),
% 2.13/2.38      inference('sup+', [status(thm)], ['69', '70'])).
% 2.13/2.38  thf('72', plain,
% 2.13/2.38      (![X0 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (k1_xboole_0))),
% 2.13/2.38      inference('sup+', [status(thm)], ['68', '71'])).
% 2.13/2.38  thf('73', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.13/2.38      inference('demod', [status(thm)], ['28', '31'])).
% 2.13/2.38  thf('74', plain,
% 2.13/2.38      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.13/2.38      inference('demod', [status(thm)], ['72', '73'])).
% 2.13/2.38  thf('75', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 2.13/2.38      inference('demod', [status(thm)], ['67', '74'])).
% 2.13/2.38  thf('76', plain,
% 2.13/2.38      (![X12 : $i, X13 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 2.13/2.38           = (k3_xboole_0 @ X12 @ X13))),
% 2.13/2.38      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.13/2.38  thf('77', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 2.13/2.38           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 2.13/2.38      inference('sup+', [status(thm)], ['75', '76'])).
% 2.13/2.38  thf('78', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 2.13/2.38      inference('cnf', [status(esa)], [t3_boole])).
% 2.13/2.38  thf('79', plain,
% 2.13/2.38      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.13/2.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.13/2.38  thf('80', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ X0 @ X1)
% 2.13/2.38           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.13/2.38      inference('demod', [status(thm)], ['77', '78', '79'])).
% 2.13/2.38  thf('81', plain,
% 2.13/2.38      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 2.13/2.38        | (r1_xboole_0 @ sk_A @ sk_C))),
% 2.13/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.38  thf('82', plain,
% 2.13/2.38      (((r1_xboole_0 @ sk_A @ sk_C)) <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 2.13/2.38      inference('split', [status(esa)], ['81'])).
% 2.13/2.38  thf('83', plain,
% 2.13/2.38      (![X4 : $i, X5 : $i]:
% 2.13/2.38         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 2.13/2.38      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.13/2.38  thf('84', plain,
% 2.13/2.38      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 2.13/2.38      inference('sup-', [status(thm)], ['82', '83'])).
% 2.13/2.38  thf('85', plain,
% 2.13/2.38      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.13/2.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.13/2.38  thf('86', plain,
% 2.13/2.38      ((((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0)))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 2.13/2.38      inference('demod', [status(thm)], ['84', '85'])).
% 2.13/2.38  thf('87', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.13/2.38           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('sup+', [status(thm)], ['7', '8'])).
% 2.13/2.38  thf('88', plain,
% 2.13/2.38      ((((k4_xboole_0 @ sk_C @ k1_xboole_0)
% 2.13/2.38          = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 2.13/2.38      inference('sup+', [status(thm)], ['86', '87'])).
% 2.13/2.38  thf('89', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 2.13/2.38      inference('cnf', [status(esa)], [t3_boole])).
% 2.13/2.38  thf('90', plain,
% 2.13/2.38      ((((sk_C) = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 2.13/2.38      inference('demod', [status(thm)], ['88', '89'])).
% 2.13/2.38  thf('91', plain,
% 2.13/2.38      ((((sk_C) = (k4_xboole_0 @ sk_C @ sk_A)))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 2.13/2.38      inference('sup+', [status(thm)], ['80', '90'])).
% 2.13/2.38  thf('92', plain,
% 2.13/2.38      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 2.13/2.38       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.13/2.38      inference('split', [status(esa)], ['81'])).
% 2.13/2.38  thf('93', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 2.13/2.38      inference('sat_resolution*', [status(thm)], ['2', '50', '62', '92'])).
% 2.13/2.38  thf('94', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 2.13/2.38      inference('simpl_trail', [status(thm)], ['91', '93'])).
% 2.13/2.38  thf('95', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('demod', [status(thm)], ['25', '32', '33'])).
% 2.13/2.38  thf('96', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.13/2.38           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('sup+', [status(thm)], ['7', '8'])).
% 2.13/2.38  thf('97', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 2.13/2.38           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 2.13/2.38      inference('sup+', [status(thm)], ['95', '96'])).
% 2.13/2.38  thf('98', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 2.13/2.38      inference('cnf', [status(esa)], [t3_boole])).
% 2.13/2.38  thf('99', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((X0)
% 2.13/2.38           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 2.13/2.38      inference('demod', [status(thm)], ['97', '98'])).
% 2.13/2.38  thf('100', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ X0 @ X1)
% 2.13/2.38           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.13/2.38      inference('demod', [status(thm)], ['77', '78', '79'])).
% 2.13/2.38  thf('101', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('demod', [status(thm)], ['99', '100'])).
% 2.13/2.38  thf('102', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C))),
% 2.13/2.38      inference('sup+', [status(thm)], ['94', '101'])).
% 2.13/2.38  thf('103', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ X0 @ X1)
% 2.13/2.38           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.13/2.38      inference('demod', [status(thm)], ['77', '78', '79'])).
% 2.13/2.38  thf('104', plain,
% 2.13/2.38      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 2.13/2.38      inference('split', [status(esa)], ['3'])).
% 2.13/2.38  thf('105', plain,
% 2.13/2.38      (![X4 : $i, X5 : $i]:
% 2.13/2.38         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 2.13/2.38      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.13/2.38  thf('106', plain,
% 2.13/2.38      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 2.13/2.38      inference('sup-', [status(thm)], ['104', '105'])).
% 2.13/2.38  thf('107', plain,
% 2.13/2.38      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.13/2.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.13/2.38  thf('108', plain,
% 2.13/2.38      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 2.13/2.38      inference('demod', [status(thm)], ['106', '107'])).
% 2.13/2.38  thf('109', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.13/2.38           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('sup+', [status(thm)], ['7', '8'])).
% 2.13/2.38  thf('110', plain,
% 2.13/2.38      ((((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 2.13/2.38          = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A))))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 2.13/2.38      inference('sup+', [status(thm)], ['108', '109'])).
% 2.13/2.38  thf('111', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 2.13/2.38      inference('cnf', [status(esa)], [t3_boole])).
% 2.13/2.38  thf('112', plain,
% 2.13/2.38      ((((sk_B) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A))))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 2.13/2.38      inference('demod', [status(thm)], ['110', '111'])).
% 2.13/2.38  thf('113', plain,
% 2.13/2.38      ((((sk_B) = (k4_xboole_0 @ sk_B @ sk_A)))
% 2.13/2.38         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 2.13/2.38      inference('sup+', [status(thm)], ['103', '112'])).
% 2.13/2.38  thf('114', plain,
% 2.13/2.38      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 2.13/2.38       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.13/2.38      inference('split', [status(esa)], ['3'])).
% 2.13/2.38  thf('115', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 2.13/2.38      inference('sat_resolution*', [status(thm)], ['2', '50', '62', '114'])).
% 2.13/2.38  thf('116', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 2.13/2.38      inference('simpl_trail', [status(thm)], ['113', '115'])).
% 2.13/2.38  thf('117', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('demod', [status(thm)], ['99', '100'])).
% 2.13/2.38  thf('118', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 2.13/2.38      inference('sup+', [status(thm)], ['116', '117'])).
% 2.13/2.38  thf('119', plain,
% 2.13/2.38      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.13/2.38         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 2.13/2.38           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.13/2.38      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.13/2.38  thf('120', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.13/2.38      inference('simplify', [status(thm)], ['36'])).
% 2.13/2.38  thf('121', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.38         (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 2.13/2.38          (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 2.13/2.38      inference('sup+', [status(thm)], ['119', '120'])).
% 2.13/2.38  thf('122', plain,
% 2.13/2.38      (![X0 : $i]:
% 2.13/2.38         (r1_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ (k4_xboole_0 @ sk_A @ X0))),
% 2.13/2.38      inference('sup+', [status(thm)], ['118', '121'])).
% 2.13/2.38  thf('123', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 2.13/2.38      inference('sup+', [status(thm)], ['102', '122'])).
% 2.13/2.38  thf('124', plain,
% 2.13/2.38      (![X4 : $i, X5 : $i]:
% 2.13/2.38         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 2.13/2.38      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.13/2.38  thf('125', plain,
% 2.13/2.38      (((k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A) = (k1_xboole_0))),
% 2.13/2.38      inference('sup-', [status(thm)], ['123', '124'])).
% 2.13/2.38  thf('126', plain,
% 2.13/2.38      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.13/2.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.13/2.38  thf('127', plain,
% 2.13/2.38      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 2.13/2.38      inference('demod', [status(thm)], ['125', '126'])).
% 2.13/2.38  thf('128', plain,
% 2.13/2.38      (![X4 : $i, X6 : $i]:
% 2.13/2.38         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 2.13/2.38      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.13/2.38  thf('129', plain,
% 2.13/2.38      ((((k1_xboole_0) != (k1_xboole_0))
% 2.13/2.38        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.13/2.38      inference('sup-', [status(thm)], ['127', '128'])).
% 2.13/2.38  thf('130', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 2.13/2.38      inference('simplify', [status(thm)], ['129'])).
% 2.13/2.38  thf('131', plain, ($false), inference('demod', [status(thm)], ['64', '130'])).
% 2.13/2.38  
% 2.13/2.38  % SZS output end Refutation
% 2.13/2.38  
% 2.22/2.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
