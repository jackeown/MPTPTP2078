%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.snxBxVR8BN

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:55 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 574 expanded)
%              Number of leaves         :   17 ( 195 expanded)
%              Depth                    :   29
%              Number of atoms          : 1163 (4756 expanded)
%              Number of equality atoms :  145 ( 581 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t71_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ B ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ C @ B ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_C @ k1_xboole_0 ) @ sk_B )
    = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('32',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','44'])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('50',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('54',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('55',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','19','55'])).

thf('57',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('58',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('62',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('64',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('68',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('71',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_C @ sk_A ) )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['66','69','72'])).

thf('74',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('75',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_C @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('77',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ X0 ) )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('84',plain,
    ( ( k3_xboole_0 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['17','18'])).

thf('85',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('88',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('92',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('94',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('96',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('98',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('100',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('102',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('104',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('106',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('108',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('110',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['92','93','110'])).

thf('112',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('114',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('115',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['113','116'])).

thf('118',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['112','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['113','116'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('121',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['104','105'])).

thf('123',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('125',plain,
    ( ( k2_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('127',plain,
    ( ( k3_xboole_0 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['17','18'])).

thf('128',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('129',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ k1_xboole_0 ) )
    = sk_C ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('131',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('133',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['125','126','131','132'])).

thf('134',plain,(
    sk_C = sk_A ),
    inference('sup+',[status(thm)],['111','133'])).

thf('135',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['134','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.snxBxVR8BN
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 15:21:41 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.60/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.80  % Solved by: fo/fo7.sh
% 0.60/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.80  % done 705 iterations in 0.366s
% 0.60/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.80  % SZS output start Refutation
% 0.60/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.60/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.80  thf(t71_xboole_1, conjecture,
% 0.60/0.80    (![A:$i,B:$i,C:$i]:
% 0.60/0.80     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.60/0.80         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.60/0.80       ( ( A ) = ( C ) ) ))).
% 0.60/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.80    (~( ![A:$i,B:$i,C:$i]:
% 0.60/0.80        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.60/0.80            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.60/0.80          ( ( A ) = ( C ) ) ) )),
% 0.60/0.80    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.60/0.80  thf('0', plain,
% 0.60/0.80      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf(t3_boole, axiom,
% 0.60/0.80    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.60/0.80  thf('1', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.60/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.60/0.80  thf(t48_xboole_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.60/0.80  thf('2', plain,
% 0.60/0.80      (![X13 : $i, X14 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.60/0.80           = (k3_xboole_0 @ X13 @ X14))),
% 0.60/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.80  thf('3', plain,
% 0.60/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['1', '2'])).
% 0.60/0.80  thf(t41_xboole_1, axiom,
% 0.60/0.80    (![A:$i,B:$i,C:$i]:
% 0.60/0.80     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.60/0.80       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.60/0.80  thf('4', plain,
% 0.60/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.60/0.80           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.60/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.60/0.80  thf('5', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 0.60/0.80           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['3', '4'])).
% 0.60/0.80  thf('6', plain,
% 0.60/0.80      (((k4_xboole_0 @ (k3_xboole_0 @ sk_C @ k1_xboole_0) @ sk_B)
% 0.60/0.80         = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['0', '5'])).
% 0.60/0.80  thf('7', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf(d7_xboole_0, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.60/0.80       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.60/0.80  thf('8', plain,
% 0.60/0.80      (![X2 : $i, X3 : $i]:
% 0.60/0.80         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.60/0.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.80  thf('9', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.80  thf(t47_xboole_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.60/0.80  thf('10', plain,
% 0.60/0.80      (![X11 : $i, X12 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.60/0.80           = (k4_xboole_0 @ X11 @ X12))),
% 0.60/0.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.60/0.80  thf('11', plain,
% 0.60/0.80      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.60/0.80      inference('sup+', [status(thm)], ['9', '10'])).
% 0.60/0.80  thf('12', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.60/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.60/0.80  thf('13', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['11', '12'])).
% 0.60/0.80  thf('14', plain,
% 0.60/0.80      (![X13 : $i, X14 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.60/0.80           = (k3_xboole_0 @ X13 @ X14))),
% 0.60/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.80  thf('15', plain,
% 0.60/0.80      (((k4_xboole_0 @ sk_C @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.60/0.80      inference('sup+', [status(thm)], ['13', '14'])).
% 0.60/0.80  thf('16', plain,
% 0.60/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['1', '2'])).
% 0.60/0.80  thf('17', plain,
% 0.60/0.80      (((k3_xboole_0 @ sk_C @ k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['15', '16'])).
% 0.60/0.80  thf('18', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.80  thf('19', plain, (((k3_xboole_0 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['17', '18'])).
% 0.60/0.80  thf('20', plain,
% 0.60/0.80      (![X13 : $i, X14 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.60/0.80           = (k3_xboole_0 @ X13 @ X14))),
% 0.60/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.80  thf('21', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.60/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.60/0.80  thf('22', plain,
% 0.60/0.80      (![X11 : $i, X12 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.60/0.80           = (k4_xboole_0 @ X11 @ X12))),
% 0.60/0.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.60/0.80  thf(t39_xboole_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.60/0.80  thf('23', plain,
% 0.60/0.80      (![X5 : $i, X6 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.60/0.80           = (k2_xboole_0 @ X5 @ X6))),
% 0.60/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.60/0.80  thf('24', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.60/0.80           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.60/0.80      inference('sup+', [status(thm)], ['22', '23'])).
% 0.60/0.80  thf(commutativity_k2_xboole_0, axiom,
% 0.60/0.80    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.60/0.80  thf('25', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.80  thf('26', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.60/0.80           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.60/0.80      inference('demod', [status(thm)], ['24', '25'])).
% 0.60/0.80  thf(t51_xboole_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.60/0.80       ( A ) ))).
% 0.60/0.80  thf('27', plain,
% 0.60/0.80      (![X15 : $i, X16 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 0.60/0.80           = (X15))),
% 0.60/0.80      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.60/0.80  thf('28', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.60/0.80      inference('sup+', [status(thm)], ['26', '27'])).
% 0.60/0.80  thf('29', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.80  thf('30', plain,
% 0.60/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.60/0.80           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.60/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.60/0.80  thf('31', plain,
% 0.60/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['1', '2'])).
% 0.60/0.80  thf('32', plain,
% 0.60/0.80      (![X2 : $i, X4 : $i]:
% 0.60/0.80         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.60/0.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.80  thf('33', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (((k4_xboole_0 @ X0 @ X0) != (k1_xboole_0))
% 0.60/0.80          | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['31', '32'])).
% 0.60/0.80  thf('34', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         (((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.60/0.80            != (k1_xboole_0))
% 0.60/0.80          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['30', '33'])).
% 0.60/0.80  thf('35', plain,
% 0.60/0.80      (![X5 : $i, X6 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.60/0.80           = (k2_xboole_0 @ X5 @ X6))),
% 0.60/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.60/0.80  thf('36', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         (((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) != (k1_xboole_0))
% 0.60/0.80          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.60/0.80      inference('demod', [status(thm)], ['34', '35'])).
% 0.60/0.80  thf('37', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         (((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.60/0.80          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['29', '36'])).
% 0.60/0.80  thf('38', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         (((k4_xboole_0 @ X0 @ X0) != (k1_xboole_0))
% 0.60/0.80          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.60/0.80             k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['28', '37'])).
% 0.60/0.80  thf('39', plain,
% 0.60/0.80      (![X11 : $i, X12 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.60/0.80           = (k4_xboole_0 @ X11 @ X12))),
% 0.60/0.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.60/0.80  thf('40', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         (((k4_xboole_0 @ X0 @ X0) != (k1_xboole_0))
% 0.60/0.80          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 0.60/0.80      inference('demod', [status(thm)], ['38', '39'])).
% 0.60/0.80  thf('41', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (((k1_xboole_0) != (k1_xboole_0))
% 0.60/0.80          | (r1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['21', '40'])).
% 0.60/0.80  thf('42', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (r1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.60/0.80      inference('simplify', [status(thm)], ['41'])).
% 0.60/0.80  thf('43', plain,
% 0.60/0.80      (![X2 : $i, X3 : $i]:
% 0.60/0.80         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.60/0.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.80  thf('44', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((k3_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.60/0.80           = (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['42', '43'])).
% 0.60/0.80  thf('45', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((k3_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.60/0.80           = (k1_xboole_0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['20', '44'])).
% 0.60/0.80  thf('46', plain,
% 0.60/0.80      (![X15 : $i, X16 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 0.60/0.80           = (X15))),
% 0.60/0.80      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.60/0.80  thf('47', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ k1_xboole_0 @ 
% 0.60/0.80           (k4_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))
% 0.60/0.80           = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['45', '46'])).
% 0.60/0.80  thf('48', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.60/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.60/0.80  thf('49', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.60/0.80      inference('sup+', [status(thm)], ['26', '27'])).
% 0.60/0.80  thf('50', plain,
% 0.60/0.80      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.60/0.80      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.60/0.80  thf('51', plain,
% 0.60/0.80      (![X11 : $i, X12 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.60/0.80           = (k4_xboole_0 @ X11 @ X12))),
% 0.60/0.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.60/0.80  thf('52', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.60/0.80           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['50', '51'])).
% 0.60/0.80  thf('53', plain,
% 0.60/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['1', '2'])).
% 0.60/0.80  thf('54', plain,
% 0.60/0.80      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.60/0.80      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.60/0.80  thf('55', plain,
% 0.60/0.80      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.60/0.80      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.60/0.80  thf('56', plain,
% 0.60/0.80      (((k1_xboole_0) = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.60/0.80      inference('demod', [status(thm)], ['6', '19', '55'])).
% 0.60/0.80  thf('57', plain,
% 0.60/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.60/0.80           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.60/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.60/0.80  thf('58', plain,
% 0.60/0.80      (![X5 : $i, X6 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.60/0.80           = (k2_xboole_0 @ X5 @ X6))),
% 0.60/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.60/0.80  thf('59', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.60/0.80           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['57', '58'])).
% 0.60/0.80  thf('60', plain,
% 0.60/0.80      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.60/0.80         = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['56', '59'])).
% 0.60/0.80  thf('61', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.80  thf('62', plain,
% 0.60/0.80      (((k2_xboole_0 @ k1_xboole_0 @ sk_B)
% 0.60/0.80         = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.60/0.80      inference('demod', [status(thm)], ['60', '61'])).
% 0.60/0.80  thf('63', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['11', '12'])).
% 0.60/0.80  thf('64', plain,
% 0.60/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.60/0.80           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.60/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.60/0.80  thf('65', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ sk_C @ X0)
% 0.60/0.80           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['63', '64'])).
% 0.60/0.80  thf('66', plain,
% 0.60/0.80      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))
% 0.60/0.80         = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ k1_xboole_0 @ sk_B)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['62', '65'])).
% 0.60/0.80  thf('67', plain,
% 0.60/0.80      (![X11 : $i, X12 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.60/0.80           = (k4_xboole_0 @ X11 @ X12))),
% 0.60/0.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.60/0.80  thf('68', plain,
% 0.60/0.80      (![X13 : $i, X14 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.60/0.80           = (k3_xboole_0 @ X13 @ X14))),
% 0.60/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.80  thf('69', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.60/0.80           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['67', '68'])).
% 0.60/0.80  thf('70', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.60/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.60/0.80  thf('71', plain,
% 0.60/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.60/0.80           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.60/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.60/0.80  thf('72', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X0 @ X1)
% 0.60/0.80           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['70', '71'])).
% 0.60/0.80  thf('73', plain,
% 0.60/0.80      (((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_C @ sk_A))
% 0.60/0.80         = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['66', '69', '72'])).
% 0.60/0.80  thf('74', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['11', '12'])).
% 0.60/0.80  thf('75', plain,
% 0.60/0.80      (((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_C @ sk_A)) = (sk_C))),
% 0.60/0.80      inference('demod', [status(thm)], ['73', '74'])).
% 0.60/0.80  thf('76', plain,
% 0.60/0.80      (![X11 : $i, X12 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.60/0.80           = (k4_xboole_0 @ X11 @ X12))),
% 0.60/0.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.60/0.80  thf('77', plain,
% 0.60/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.60/0.80           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.60/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.60/0.80  thf('78', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.60/0.80           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['76', '77'])).
% 0.60/0.80  thf('79', plain,
% 0.60/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.60/0.80           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.60/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.60/0.80  thf('80', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 0.60/0.80           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 0.60/0.80      inference('demod', [status(thm)], ['78', '79'])).
% 0.60/0.80  thf('81', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ sk_C @ 
% 0.60/0.80           (k2_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ X0))
% 0.60/0.80           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['75', '80'])).
% 0.60/0.80  thf('82', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 0.60/0.80           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 0.60/0.80      inference('demod', [status(thm)], ['78', '79'])).
% 0.60/0.80  thf('83', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 0.60/0.80           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['3', '4'])).
% 0.60/0.80  thf('84', plain, (((k3_xboole_0 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['17', '18'])).
% 0.60/0.80  thf('85', plain,
% 0.60/0.80      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.60/0.80      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.60/0.80  thf('86', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))),
% 0.60/0.80      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 0.60/0.80  thf('87', plain,
% 0.60/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.60/0.80           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.60/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.60/0.80  thf('88', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.60/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.60/0.80  thf('89', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.60/0.80           = (k4_xboole_0 @ X1 @ X0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['87', '88'])).
% 0.60/0.80  thf('90', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.60/0.80      inference('sup+', [status(thm)], ['86', '89'])).
% 0.60/0.80  thf('91', plain,
% 0.60/0.80      (![X5 : $i, X6 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.60/0.80           = (k2_xboole_0 @ X5 @ X6))),
% 0.60/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.60/0.80  thf('92', plain,
% 0.60/0.80      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_C))),
% 0.60/0.80      inference('sup+', [status(thm)], ['90', '91'])).
% 0.60/0.80  thf('93', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.80  thf('94', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('95', plain,
% 0.60/0.80      (![X2 : $i, X3 : $i]:
% 0.60/0.80         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.60/0.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.80  thf('96', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['94', '95'])).
% 0.60/0.80  thf('97', plain,
% 0.60/0.80      (![X11 : $i, X12 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.60/0.80           = (k4_xboole_0 @ X11 @ X12))),
% 0.60/0.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.60/0.80  thf('98', plain,
% 0.60/0.80      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.60/0.80      inference('sup+', [status(thm)], ['96', '97'])).
% 0.60/0.80  thf('99', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.60/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.60/0.80  thf('100', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['98', '99'])).
% 0.60/0.80  thf('101', plain,
% 0.60/0.80      (![X13 : $i, X14 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.60/0.80           = (k3_xboole_0 @ X13 @ X14))),
% 0.60/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.80  thf('102', plain,
% 0.60/0.80      (((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.60/0.80      inference('sup+', [status(thm)], ['100', '101'])).
% 0.60/0.80  thf('103', plain,
% 0.60/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['1', '2'])).
% 0.60/0.80  thf('104', plain,
% 0.60/0.80      (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['102', '103'])).
% 0.60/0.80  thf('105', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['94', '95'])).
% 0.60/0.80  thf('106', plain, (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['104', '105'])).
% 0.60/0.80  thf('107', plain,
% 0.60/0.80      (![X15 : $i, X16 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 0.60/0.80           = (X15))),
% 0.60/0.80      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.60/0.80  thf('108', plain,
% 0.60/0.80      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ k1_xboole_0))
% 0.60/0.80         = (sk_A))),
% 0.60/0.80      inference('sup+', [status(thm)], ['106', '107'])).
% 0.60/0.80  thf('109', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.60/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.60/0.80  thf('110', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_A) = (sk_A))),
% 0.60/0.80      inference('demod', [status(thm)], ['108', '109'])).
% 0.60/0.80  thf('111', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_C))),
% 0.60/0.80      inference('demod', [status(thm)], ['92', '93', '110'])).
% 0.60/0.80  thf('112', plain,
% 0.60/0.80      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('113', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.80  thf('114', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['98', '99'])).
% 0.60/0.80  thf('115', plain,
% 0.60/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.60/0.80           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.60/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.60/0.80  thf('116', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ sk_A @ X0)
% 0.60/0.80           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['114', '115'])).
% 0.60/0.80  thf('117', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ sk_A @ X0)
% 0.60/0.80           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['113', '116'])).
% 0.60/0.80  thf('118', plain,
% 0.60/0.80      (((k4_xboole_0 @ sk_A @ sk_C)
% 0.60/0.80         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['112', '117'])).
% 0.60/0.80  thf('119', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((k4_xboole_0 @ sk_A @ X0)
% 0.60/0.80           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['113', '116'])).
% 0.60/0.80  thf('120', plain,
% 0.60/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['1', '2'])).
% 0.60/0.80  thf('121', plain,
% 0.60/0.80      (((k4_xboole_0 @ sk_A @ sk_C) = (k3_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.60/0.80      inference('demod', [status(thm)], ['118', '119', '120'])).
% 0.60/0.80  thf('122', plain, (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['104', '105'])).
% 0.60/0.80  thf('123', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.60/0.80      inference('demod', [status(thm)], ['121', '122'])).
% 0.60/0.80  thf('124', plain,
% 0.60/0.80      (![X5 : $i, X6 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.60/0.80           = (k2_xboole_0 @ X5 @ X6))),
% 0.60/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.60/0.80  thf('125', plain,
% 0.60/0.80      (((k2_xboole_0 @ sk_C @ k1_xboole_0) = (k2_xboole_0 @ sk_C @ sk_A))),
% 0.60/0.80      inference('sup+', [status(thm)], ['123', '124'])).
% 0.60/0.80  thf('126', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.80  thf('127', plain, (((k3_xboole_0 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['17', '18'])).
% 0.60/0.80  thf('128', plain,
% 0.60/0.80      (![X15 : $i, X16 : $i]:
% 0.60/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 0.60/0.80           = (X15))),
% 0.60/0.80      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.60/0.80  thf('129', plain,
% 0.60/0.80      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ k1_xboole_0))
% 0.60/0.80         = (sk_C))),
% 0.60/0.80      inference('sup+', [status(thm)], ['127', '128'])).
% 0.60/0.80  thf('130', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.60/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.60/0.80  thf('131', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_C) = (sk_C))),
% 0.60/0.80      inference('demod', [status(thm)], ['129', '130'])).
% 0.60/0.80  thf('132', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.80  thf('133', plain, (((sk_C) = (k2_xboole_0 @ sk_A @ sk_C))),
% 0.60/0.80      inference('demod', [status(thm)], ['125', '126', '131', '132'])).
% 0.60/0.80  thf('134', plain, (((sk_C) = (sk_A))),
% 0.60/0.80      inference('sup+', [status(thm)], ['111', '133'])).
% 0.60/0.80  thf('135', plain, (((sk_A) != (sk_C))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('136', plain, ($false),
% 0.60/0.80      inference('simplify_reflect-', [status(thm)], ['134', '135'])).
% 0.60/0.80  
% 0.60/0.80  % SZS output end Refutation
% 0.60/0.80  
% 0.60/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
