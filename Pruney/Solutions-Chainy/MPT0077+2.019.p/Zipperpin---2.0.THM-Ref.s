%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7yV2bQC8T9

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 466 expanded)
%              Number of leaves         :   16 ( 143 expanded)
%              Depth                    :   24
%              Number of atoms          :  831 (4925 expanded)
%              Number of equality atoms :   65 ( 324 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

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
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','11'])).

thf('13',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','11'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('15',plain,
    ( ( ( k2_xboole_0 @ sk_C @ sk_A )
      = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
        = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_C @ sk_A ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_A ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) @ sk_A ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','11'])).

thf('23',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
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
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','21','22','27'])).

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
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('36',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('40',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','11'])).

thf('42',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('46',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('48',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['2','33','51'])).

thf('53',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','52'])).

thf('54',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('57',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['54'])).

thf('59',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','33','51','58'])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['57','59'])).

thf('61',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('62',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('63',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','33','51','62'])).

thf('64',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['61','63'])).

thf('65',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('66',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','74'])).

thf('76',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('77',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['53','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7yV2bQC8T9
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:31:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 193 iterations in 0.122s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(t70_xboole_1, conjecture,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.20/0.58            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.20/0.58       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.58            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.58        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.20/0.58               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.20/0.58          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.58               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      ((~ (r1_xboole_0 @ sk_A @ sk_C)
% 0.20/0.58        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 0.20/0.58        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain,
% 0.20/0.58      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.58         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.20/0.58       ~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf(t41_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.58       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.20/0.58           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.20/0.58        | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('split', [status(esa)], ['4'])).
% 0.20/0.58  thf(d7_xboole_0, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.58       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (![X2 : $i, X3 : $i]:
% 0.20/0.58         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.20/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.58  thf(t47_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.58  thf('8', plain,
% 0.20/0.58      (![X12 : $i, X13 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.20/0.58           = (k4_xboole_0 @ X12 @ X13))),
% 0.20/0.58      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.58  thf('9', plain,
% 0.20/0.58      ((((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.20/0.58          = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.58  thf(t3_boole, axiom,
% 0.20/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.58  thf('10', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      ((((sk_A) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      ((((sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['3', '11'])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      ((((sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['3', '11'])).
% 0.20/0.58  thf(t39_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      (![X6 : $i, X7 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.20/0.58           = (k2_xboole_0 @ X6 @ X7))),
% 0.20/0.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      ((((k2_xboole_0 @ sk_C @ sk_A)
% 0.20/0.58          = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.20/0.58           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 0.20/0.58            (k4_xboole_0 @ sk_A @ sk_B))
% 0.20/0.58            = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_C @ sk_A))))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.20/0.58           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.20/0.58  thf('19', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 0.20/0.58            (k4_xboole_0 @ sk_A @ sk_B))
% 0.20/0.58            = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_A)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      ((((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.20/0.58          = (k4_xboole_0 @ 
% 0.20/0.58             (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C) @ sk_A)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['12', '19'])).
% 0.20/0.58  thf(t48_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.58  thf('21', plain,
% 0.20/0.58      (![X14 : $i, X15 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.20/0.58           = (k3_xboole_0 @ X14 @ X15))),
% 0.20/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      ((((sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['3', '11'])).
% 0.20/0.58  thf('23', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      (![X14 : $i, X15 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.20/0.58           = (k3_xboole_0 @ X14 @ X15))),
% 0.20/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.58  thf('25', plain,
% 0.20/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.58  thf(t2_boole, axiom,
% 0.20/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.58  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.58  thf('28', plain,
% 0.20/0.58      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('demod', [status(thm)], ['20', '21', '22', '27'])).
% 0.20/0.58  thf('29', plain,
% 0.20/0.58      (![X2 : $i, X4 : $i]:
% 0.20/0.58         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('33', plain,
% 0.20/0.58      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.20/0.58       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('split', [status(esa)], ['4'])).
% 0.20/0.58  thf('35', plain,
% 0.20/0.58      (![X2 : $i, X3 : $i]:
% 0.20/0.58         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.20/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.58  thf('37', plain,
% 0.20/0.58      (![X12 : $i, X13 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.20/0.58           = (k4_xboole_0 @ X12 @ X13))),
% 0.20/0.58      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.58  thf('38', plain,
% 0.20/0.58      ((((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.58  thf('39', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.58  thf('40', plain,
% 0.20/0.58      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_B)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      ((((sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['3', '11'])).
% 0.20/0.58  thf('42', plain,
% 0.20/0.58      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_C)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.20/0.58             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.58  thf('43', plain,
% 0.20/0.58      (![X14 : $i, X15 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.20/0.58           = (k3_xboole_0 @ X14 @ X15))),
% 0.20/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.58  thf('44', plain,
% 0.20/0.58      ((((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.20/0.58             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.58  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.58  thf('46', plain,
% 0.20/0.58      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.20/0.58             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.58  thf('47', plain,
% 0.20/0.58      (![X2 : $i, X4 : $i]:
% 0.20/0.58         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.58  thf('48', plain,
% 0.20/0.58      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.20/0.58             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.58  thf('49', plain,
% 0.20/0.58      (((r1_xboole_0 @ sk_A @ sk_C))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.20/0.58             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.58  thf('50', plain,
% 0.20/0.58      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('51', plain,
% 0.20/0.58      (((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.20/0.58       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.58  thf('52', plain, (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['2', '33', '51'])).
% 0.20/0.58  thf('53', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['1', '52'])).
% 0.20/0.58  thf('54', plain,
% 0.20/0.58      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.20/0.58        | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('55', plain,
% 0.20/0.58      (((r1_xboole_0 @ sk_A @ sk_C)) <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.20/0.58      inference('split', [status(esa)], ['54'])).
% 0.20/0.58  thf('56', plain,
% 0.20/0.58      (![X2 : $i, X3 : $i]:
% 0.20/0.58         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.20/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.58  thf('57', plain,
% 0.20/0.58      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.58  thf('58', plain,
% 0.20/0.58      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.20/0.58       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.58      inference('split', [status(esa)], ['54'])).
% 0.20/0.58  thf('59', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['2', '33', '51', '58'])).
% 0.20/0.58  thf('60', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['57', '59'])).
% 0.20/0.58  thf('61', plain,
% 0.20/0.58      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_B)))
% 0.20/0.58         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.58  thf('62', plain,
% 0.20/0.58      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.20/0.58       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.58      inference('split', [status(esa)], ['4'])).
% 0.20/0.58  thf('63', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['2', '33', '51', '62'])).
% 0.20/0.58  thf('64', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['61', '63'])).
% 0.20/0.58  thf('65', plain,
% 0.20/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.20/0.58           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.20/0.58  thf('66', plain,
% 0.20/0.58      (![X14 : $i, X15 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.20/0.58           = (k3_xboole_0 @ X14 @ X15))),
% 0.20/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.58  thf('67', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.20/0.58           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['65', '66'])).
% 0.20/0.58  thf('68', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 0.20/0.58           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['64', '67'])).
% 0.20/0.58  thf('69', plain,
% 0.20/0.58      (![X12 : $i, X13 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.20/0.58           = (k4_xboole_0 @ X12 @ X13))),
% 0.20/0.58      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.58  thf('70', plain,
% 0.20/0.58      (![X14 : $i, X15 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.20/0.58           = (k3_xboole_0 @ X14 @ X15))),
% 0.20/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.58  thf('71', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.58           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['69', '70'])).
% 0.20/0.58  thf('72', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0))
% 0.20/0.58           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['68', '71'])).
% 0.20/0.58  thf('73', plain,
% 0.20/0.58      (![X2 : $i, X4 : $i]:
% 0.20/0.58         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.58  thf('74', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0)) != (k1_xboole_0))
% 0.20/0.58          | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.58  thf('75', plain,
% 0.20/0.58      ((((k3_xboole_0 @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.58        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['60', '74'])).
% 0.20/0.58  thf('76', plain,
% 0.20/0.58      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.58  thf('77', plain,
% 0.20/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.58        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.58      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.58  thf('78', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.58      inference('simplify', [status(thm)], ['77'])).
% 0.20/0.58  thf('79', plain, ($false), inference('demod', [status(thm)], ['53', '78'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
