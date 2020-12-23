%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ajaDbqMgG5

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:50 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 568 expanded)
%              Number of leaves         :   17 ( 175 expanded)
%              Depth                    :   25
%              Number of atoms          :  827 (5766 expanded)
%              Number of equality atoms :   70 ( 426 expanded)
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
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('20',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('30',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('40',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('44',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['2','33','49'])).

thf('51',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('52',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('55',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['52'])).

thf('57',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','33','49','56'])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['55','57'])).

thf('59',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('61',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('63',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('67',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','33','49','66'])).

thf('68',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('72',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['51','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ajaDbqMgG5
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:46:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.51/1.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.51/1.69  % Solved by: fo/fo7.sh
% 1.51/1.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.69  % done 609 iterations in 1.196s
% 1.51/1.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.51/1.69  % SZS output start Refutation
% 1.51/1.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.51/1.69  thf(sk_C_type, type, sk_C: $i).
% 1.51/1.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.51/1.69  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.51/1.69  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.51/1.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.51/1.69  thf(t70_xboole_1, conjecture,
% 1.51/1.69    (![A:$i,B:$i,C:$i]:
% 1.51/1.69     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.51/1.69            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.51/1.69       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.51/1.69            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.51/1.69  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.69    (~( ![A:$i,B:$i,C:$i]:
% 1.51/1.69        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.51/1.69               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.51/1.69          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.51/1.69               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 1.51/1.69    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 1.51/1.69  thf('0', plain,
% 1.51/1.69      ((~ (r1_xboole_0 @ sk_A @ sk_C)
% 1.51/1.69        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 1.51/1.69        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.51/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.69  thf('1', plain,
% 1.51/1.69      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 1.51/1.69         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.69      inference('split', [status(esa)], ['0'])).
% 1.51/1.69  thf('2', plain,
% 1.51/1.69      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 1.51/1.69       ~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 1.51/1.69      inference('split', [status(esa)], ['0'])).
% 1.51/1.69  thf('3', plain,
% 1.51/1.69      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 1.51/1.69        | (r1_xboole_0 @ sk_A @ sk_B))),
% 1.51/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.69  thf('4', plain,
% 1.51/1.69      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 1.51/1.69         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.69      inference('split', [status(esa)], ['3'])).
% 1.51/1.69  thf(d7_xboole_0, axiom,
% 1.51/1.69    (![A:$i,B:$i]:
% 1.51/1.69     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.51/1.69       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.51/1.69  thf('5', plain,
% 1.51/1.69      (![X2 : $i, X3 : $i]:
% 1.51/1.69         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.51/1.69      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.51/1.69  thf('6', plain,
% 1.51/1.69      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 1.51/1.69         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.69      inference('sup-', [status(thm)], ['4', '5'])).
% 1.51/1.69  thf(t47_xboole_1, axiom,
% 1.51/1.69    (![A:$i,B:$i]:
% 1.51/1.69     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.51/1.69  thf('7', plain,
% 1.51/1.69      (![X11 : $i, X12 : $i]:
% 1.51/1.69         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 1.51/1.70           = (k4_xboole_0 @ X11 @ X12))),
% 1.51/1.70      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.51/1.70  thf('8', plain,
% 1.51/1.70      ((((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 1.51/1.70          = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('sup+', [status(thm)], ['6', '7'])).
% 1.51/1.70  thf(t3_boole, axiom,
% 1.51/1.70    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.51/1.70  thf('9', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.51/1.70      inference('cnf', [status(esa)], [t3_boole])).
% 1.51/1.70  thf('10', plain,
% 1.51/1.70      ((((sk_A) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('demod', [status(thm)], ['8', '9'])).
% 1.51/1.70  thf(commutativity_k2_xboole_0, axiom,
% 1.51/1.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.51/1.70  thf('11', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.51/1.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.51/1.70  thf(t41_xboole_1, axiom,
% 1.51/1.70    (![A:$i,B:$i,C:$i]:
% 1.51/1.70     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.51/1.70       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.51/1.70  thf('12', plain,
% 1.51/1.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 1.51/1.70           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 1.51/1.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.51/1.70  thf('13', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 1.51/1.70           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.51/1.70      inference('sup+', [status(thm)], ['11', '12'])).
% 1.51/1.70  thf('14', plain,
% 1.51/1.70      ((((sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('demod', [status(thm)], ['10', '13'])).
% 1.51/1.70  thf(idempotence_k2_xboole_0, axiom,
% 1.51/1.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.51/1.70  thf('15', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 1.51/1.70      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.51/1.70  thf('16', plain,
% 1.51/1.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 1.51/1.70           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 1.51/1.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.51/1.70  thf('17', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.51/1.70           = (k4_xboole_0 @ X1 @ X0))),
% 1.51/1.70      inference('sup+', [status(thm)], ['15', '16'])).
% 1.51/1.70  thf('18', plain,
% 1.51/1.70      ((((k4_xboole_0 @ sk_A @ sk_B)
% 1.51/1.70          = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('sup+', [status(thm)], ['14', '17'])).
% 1.51/1.70  thf('19', plain,
% 1.51/1.70      ((((sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('demod', [status(thm)], ['10', '13'])).
% 1.51/1.70  thf('20', plain,
% 1.51/1.70      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_B)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('sup+', [status(thm)], ['18', '19'])).
% 1.51/1.70  thf(t48_xboole_1, axiom,
% 1.51/1.70    (![A:$i,B:$i]:
% 1.51/1.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.51/1.70  thf('21', plain,
% 1.51/1.70      (![X13 : $i, X14 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.51/1.70           = (k3_xboole_0 @ X13 @ X14))),
% 1.51/1.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.51/1.70  thf('22', plain,
% 1.51/1.70      ((((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_B)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('sup+', [status(thm)], ['20', '21'])).
% 1.51/1.70  thf('23', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.51/1.70      inference('cnf', [status(esa)], [t3_boole])).
% 1.51/1.70  thf('24', plain,
% 1.51/1.70      (![X13 : $i, X14 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.51/1.70           = (k3_xboole_0 @ X13 @ X14))),
% 1.51/1.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.51/1.70  thf('25', plain,
% 1.51/1.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.51/1.70      inference('sup+', [status(thm)], ['23', '24'])).
% 1.51/1.70  thf(t2_boole, axiom,
% 1.51/1.70    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.51/1.70  thf('26', plain,
% 1.51/1.70      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 1.51/1.70      inference('cnf', [status(esa)], [t2_boole])).
% 1.51/1.70  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.51/1.70      inference('demod', [status(thm)], ['25', '26'])).
% 1.51/1.70  thf('28', plain,
% 1.51/1.70      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('demod', [status(thm)], ['22', '27'])).
% 1.51/1.70  thf('29', plain,
% 1.51/1.70      (![X2 : $i, X4 : $i]:
% 1.51/1.70         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.51/1.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.51/1.70  thf('30', plain,
% 1.51/1.70      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('sup-', [status(thm)], ['28', '29'])).
% 1.51/1.70  thf('31', plain,
% 1.51/1.70      (((r1_xboole_0 @ sk_A @ sk_B))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('simplify', [status(thm)], ['30'])).
% 1.51/1.70  thf('32', plain,
% 1.51/1.70      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('split', [status(esa)], ['0'])).
% 1.51/1.70  thf('33', plain,
% 1.51/1.70      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 1.51/1.70       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['31', '32'])).
% 1.51/1.70  thf('34', plain,
% 1.51/1.70      ((((sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('demod', [status(thm)], ['10', '13'])).
% 1.51/1.70  thf('35', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 1.51/1.70           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.51/1.70      inference('sup+', [status(thm)], ['11', '12'])).
% 1.51/1.70  thf('36', plain,
% 1.51/1.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 1.51/1.70           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 1.51/1.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.51/1.70  thf('37', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 1.51/1.70           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.51/1.70      inference('sup+', [status(thm)], ['35', '36'])).
% 1.51/1.70  thf('38', plain,
% 1.51/1.70      ((((sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('sup+', [status(thm)], ['34', '37'])).
% 1.51/1.70  thf('39', plain,
% 1.51/1.70      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_B)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('sup+', [status(thm)], ['18', '19'])).
% 1.51/1.70  thf('40', plain,
% 1.51/1.70      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_C)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('demod', [status(thm)], ['38', '39'])).
% 1.51/1.70  thf('41', plain,
% 1.51/1.70      (![X13 : $i, X14 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.51/1.70           = (k3_xboole_0 @ X13 @ X14))),
% 1.51/1.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.51/1.70  thf('42', plain,
% 1.51/1.70      ((((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('sup+', [status(thm)], ['40', '41'])).
% 1.51/1.70  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.51/1.70      inference('demod', [status(thm)], ['25', '26'])).
% 1.51/1.70  thf('44', plain,
% 1.51/1.70      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('demod', [status(thm)], ['42', '43'])).
% 1.51/1.70  thf('45', plain,
% 1.51/1.70      (![X2 : $i, X4 : $i]:
% 1.51/1.70         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.51/1.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.51/1.70  thf('46', plain,
% 1.51/1.70      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('sup-', [status(thm)], ['44', '45'])).
% 1.51/1.70  thf('47', plain,
% 1.51/1.70      (((r1_xboole_0 @ sk_A @ sk_C))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.51/1.70      inference('simplify', [status(thm)], ['46'])).
% 1.51/1.70  thf('48', plain,
% 1.51/1.70      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.51/1.70      inference('split', [status(esa)], ['0'])).
% 1.51/1.70  thf('49', plain,
% 1.51/1.70      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 1.51/1.70       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['47', '48'])).
% 1.51/1.70  thf('50', plain, (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.51/1.70      inference('sat_resolution*', [status(thm)], ['2', '33', '49'])).
% 1.51/1.70  thf('51', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 1.51/1.70      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 1.51/1.70  thf('52', plain,
% 1.51/1.70      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 1.51/1.70        | (r1_xboole_0 @ sk_A @ sk_C))),
% 1.51/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.70  thf('53', plain,
% 1.51/1.70      (((r1_xboole_0 @ sk_A @ sk_C)) <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.51/1.70      inference('split', [status(esa)], ['52'])).
% 1.51/1.70  thf('54', plain,
% 1.51/1.70      (![X2 : $i, X3 : $i]:
% 1.51/1.70         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.51/1.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.51/1.70  thf('55', plain,
% 1.51/1.70      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['53', '54'])).
% 1.51/1.70  thf('56', plain,
% 1.51/1.70      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 1.51/1.70       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.51/1.70      inference('split', [status(esa)], ['52'])).
% 1.51/1.70  thf('57', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 1.51/1.70      inference('sat_resolution*', [status(thm)], ['2', '33', '49', '56'])).
% 1.51/1.70  thf('58', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 1.51/1.70      inference('simpl_trail', [status(thm)], ['55', '57'])).
% 1.51/1.70  thf('59', plain,
% 1.51/1.70      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('split', [status(esa)], ['3'])).
% 1.51/1.70  thf('60', plain,
% 1.51/1.70      (![X2 : $i, X3 : $i]:
% 1.51/1.70         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.51/1.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.51/1.70  thf('61', plain,
% 1.51/1.70      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['59', '60'])).
% 1.51/1.70  thf('62', plain,
% 1.51/1.70      (![X11 : $i, X12 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 1.51/1.70           = (k4_xboole_0 @ X11 @ X12))),
% 1.51/1.70      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.51/1.70  thf('63', plain,
% 1.51/1.70      ((((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('sup+', [status(thm)], ['61', '62'])).
% 1.51/1.70  thf('64', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.51/1.70      inference('cnf', [status(esa)], [t3_boole])).
% 1.51/1.70  thf('65', plain,
% 1.51/1.70      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_B)))
% 1.51/1.70         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('demod', [status(thm)], ['63', '64'])).
% 1.51/1.70  thf('66', plain,
% 1.51/1.70      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 1.51/1.70       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.51/1.70      inference('split', [status(esa)], ['3'])).
% 1.51/1.70  thf('67', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 1.51/1.70      inference('sat_resolution*', [status(thm)], ['2', '33', '49', '66'])).
% 1.51/1.70  thf('68', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.51/1.70      inference('simpl_trail', [status(thm)], ['65', '67'])).
% 1.51/1.70  thf('69', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 1.51/1.70           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.51/1.70      inference('sup+', [status(thm)], ['35', '36'])).
% 1.51/1.70  thf('70', plain,
% 1.51/1.70      (![X0 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ sk_A @ X0)
% 1.51/1.70           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.51/1.70      inference('sup+', [status(thm)], ['68', '69'])).
% 1.51/1.70  thf('71', plain,
% 1.51/1.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 1.51/1.70           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 1.51/1.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.51/1.70  thf('72', plain,
% 1.51/1.70      (![X13 : $i, X14 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.51/1.70           = (k3_xboole_0 @ X13 @ X14))),
% 1.51/1.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.51/1.70  thf('73', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 1.51/1.70           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.51/1.70      inference('sup+', [status(thm)], ['71', '72'])).
% 1.51/1.70  thf('74', plain,
% 1.51/1.70      (![X0 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 1.51/1.70           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 1.51/1.70      inference('sup+', [status(thm)], ['70', '73'])).
% 1.51/1.70  thf('75', plain,
% 1.51/1.70      (![X13 : $i, X14 : $i]:
% 1.51/1.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.51/1.70           = (k3_xboole_0 @ X13 @ X14))),
% 1.51/1.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.51/1.70  thf('76', plain,
% 1.51/1.70      (![X0 : $i]:
% 1.51/1.70         ((k3_xboole_0 @ sk_A @ X0)
% 1.51/1.70           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 1.51/1.70      inference('demod', [status(thm)], ['74', '75'])).
% 1.51/1.70  thf('77', plain,
% 1.51/1.70      (![X2 : $i, X4 : $i]:
% 1.51/1.70         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.51/1.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.51/1.70  thf('78', plain,
% 1.51/1.70      (![X0 : $i]:
% 1.51/1.70         (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 1.51/1.70          | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['76', '77'])).
% 1.51/1.70  thf('79', plain,
% 1.51/1.70      ((((k1_xboole_0) != (k1_xboole_0))
% 1.51/1.70        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['58', '78'])).
% 1.51/1.70  thf('80', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.51/1.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.51/1.70  thf('81', plain,
% 1.51/1.70      ((((k1_xboole_0) != (k1_xboole_0))
% 1.51/1.70        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.51/1.70      inference('demod', [status(thm)], ['79', '80'])).
% 1.51/1.70  thf('82', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 1.51/1.70      inference('simplify', [status(thm)], ['81'])).
% 1.51/1.70  thf('83', plain, ($false), inference('demod', [status(thm)], ['51', '82'])).
% 1.51/1.70  
% 1.51/1.70  % SZS output end Refutation
% 1.51/1.70  
% 1.51/1.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
