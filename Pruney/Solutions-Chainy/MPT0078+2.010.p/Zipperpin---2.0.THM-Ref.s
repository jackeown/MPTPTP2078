%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3DPvnc0KBS

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:53 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 277 expanded)
%              Number of leaves         :   21 ( 100 expanded)
%              Depth                    :   17
%              Number of atoms          : 1030 (2164 expanded)
%              Number of equality atoms :  122 ( 266 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('1',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('15',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21','22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13','28'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['29','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['1','39'])).

thf('41',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('43',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('51',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('56',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['59','72'])).

thf('74',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['40','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('76',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','82'])).

thf('84',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('85',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('87',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('89',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('91',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21','22','27'])).

thf('94',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','44'])).

thf('96',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('97',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('101',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('106',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_C_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','106'])).

thf('108',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['94','107'])).

thf('109',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('110',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('112',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('113',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    sk_A = sk_C_1 ),
    inference(demod,[status(thm)],['85','86','113'])).

thf('115',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['114','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3DPvnc0KBS
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:43:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.19/2.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.19/2.39  % Solved by: fo/fo7.sh
% 2.19/2.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.19/2.39  % done 4018 iterations in 1.923s
% 2.19/2.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.19/2.39  % SZS output start Refutation
% 2.19/2.39  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.19/2.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.19/2.39  thf(sk_A_type, type, sk_A: $i).
% 2.19/2.39  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.19/2.39  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.19/2.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.19/2.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.19/2.39  thf(sk_B_type, type, sk_B: $i > $i).
% 2.19/2.39  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.19/2.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.19/2.39  thf(t7_xboole_0, axiom,
% 2.19/2.39    (![A:$i]:
% 2.19/2.39     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.19/2.39          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.19/2.39  thf('0', plain,
% 2.19/2.39      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 2.19/2.39      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.19/2.39  thf(t71_xboole_1, conjecture,
% 2.19/2.39    (![A:$i,B:$i,C:$i]:
% 2.19/2.39     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 2.19/2.39         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.19/2.39       ( ( A ) = ( C ) ) ))).
% 2.19/2.39  thf(zf_stmt_0, negated_conjecture,
% 2.19/2.39    (~( ![A:$i,B:$i,C:$i]:
% 2.19/2.39        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 2.19/2.39            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.19/2.39          ( ( A ) = ( C ) ) ) )),
% 2.19/2.39    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 2.19/2.39  thf('1', plain,
% 2.19/2.39      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 2.19/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.39  thf(t3_boole, axiom,
% 2.19/2.39    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.19/2.39  thf('2', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.19/2.39      inference('cnf', [status(esa)], [t3_boole])).
% 2.19/2.39  thf(t48_xboole_1, axiom,
% 2.19/2.39    (![A:$i,B:$i]:
% 2.19/2.39     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.19/2.39  thf('3', plain,
% 2.19/2.39      (![X16 : $i, X17 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.19/2.39           = (k3_xboole_0 @ X16 @ X17))),
% 2.19/2.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.39  thf('4', plain,
% 2.19/2.39      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['2', '3'])).
% 2.19/2.39  thf(t2_boole, axiom,
% 2.19/2.39    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.19/2.39  thf('5', plain,
% 2.19/2.39      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 2.19/2.39      inference('cnf', [status(esa)], [t2_boole])).
% 2.19/2.39  thf('6', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.19/2.39      inference('demod', [status(thm)], ['4', '5'])).
% 2.19/2.39  thf('7', plain,
% 2.19/2.39      (![X16 : $i, X17 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.19/2.39           = (k3_xboole_0 @ X16 @ X17))),
% 2.19/2.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.39  thf(t41_xboole_1, axiom,
% 2.19/2.39    (![A:$i,B:$i,C:$i]:
% 2.19/2.39     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.19/2.39       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.19/2.39  thf('8', plain,
% 2.19/2.39      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 2.19/2.39           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.19/2.39  thf('9', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 2.19/2.39           = (k4_xboole_0 @ X2 @ 
% 2.19/2.39              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 2.19/2.39      inference('sup+', [status(thm)], ['7', '8'])).
% 2.19/2.39  thf('10', plain,
% 2.19/2.39      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 2.19/2.39           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.19/2.39  thf('11', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 2.19/2.39           = (k4_xboole_0 @ X2 @ 
% 2.19/2.39              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 2.19/2.39      inference('demod', [status(thm)], ['9', '10'])).
% 2.19/2.39  thf('12', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 2.19/2.39           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 2.19/2.39              (k2_xboole_0 @ X1 @ k1_xboole_0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['6', '11'])).
% 2.19/2.39  thf(commutativity_k3_xboole_0, axiom,
% 2.19/2.39    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.19/2.39  thf('13', plain,
% 2.19/2.39      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.19/2.39  thf('14', plain,
% 2.19/2.39      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 2.19/2.39           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.19/2.39  thf('15', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.19/2.39      inference('cnf', [status(esa)], [t3_boole])).
% 2.19/2.39  thf('16', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 2.19/2.39           = (k4_xboole_0 @ X1 @ X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['14', '15'])).
% 2.19/2.39  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.19/2.39      inference('demod', [status(thm)], ['4', '5'])).
% 2.19/2.39  thf('18', plain,
% 2.19/2.39      (![X0 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['16', '17'])).
% 2.19/2.39  thf('19', plain,
% 2.19/2.39      (![X16 : $i, X17 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.19/2.39           = (k3_xboole_0 @ X16 @ X17))),
% 2.19/2.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.39  thf('20', plain,
% 2.19/2.39      (![X0 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 2.19/2.39           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['18', '19'])).
% 2.19/2.39  thf('21', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.19/2.39      inference('cnf', [status(esa)], [t3_boole])).
% 2.19/2.39  thf('22', plain,
% 2.19/2.39      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.19/2.39  thf(t46_xboole_1, axiom,
% 2.19/2.39    (![A:$i,B:$i]:
% 2.19/2.39     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 2.19/2.39  thf('23', plain,
% 2.19/2.39      (![X14 : $i, X15 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 2.19/2.39      inference('cnf', [status(esa)], [t46_xboole_1])).
% 2.19/2.39  thf('24', plain,
% 2.19/2.39      (![X16 : $i, X17 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.19/2.39           = (k3_xboole_0 @ X16 @ X17))),
% 2.19/2.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.39  thf('25', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 2.19/2.39           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['23', '24'])).
% 2.19/2.39  thf('26', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.19/2.39      inference('cnf', [status(esa)], [t3_boole])).
% 2.19/2.39  thf('27', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('demod', [status(thm)], ['25', '26'])).
% 2.19/2.39  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.19/2.39      inference('demod', [status(thm)], ['20', '21', '22', '27'])).
% 2.19/2.39  thf('29', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 2.19/2.39           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 2.19/2.39      inference('demod', [status(thm)], ['12', '13', '28'])).
% 2.19/2.39  thf(commutativity_k2_xboole_0, axiom,
% 2.19/2.39    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.19/2.39  thf('30', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.19/2.39  thf('31', plain,
% 2.19/2.39      (![X14 : $i, X15 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 2.19/2.39      inference('cnf', [status(esa)], [t46_xboole_1])).
% 2.19/2.39  thf('32', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['30', '31'])).
% 2.19/2.39  thf('33', plain,
% 2.19/2.39      (![X16 : $i, X17 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.19/2.39           = (k3_xboole_0 @ X16 @ X17))),
% 2.19/2.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.39  thf('34', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 2.19/2.39           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['32', '33'])).
% 2.19/2.39  thf('35', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.19/2.39      inference('cnf', [status(esa)], [t3_boole])).
% 2.19/2.39  thf('36', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('demod', [status(thm)], ['34', '35'])).
% 2.19/2.39  thf(t49_xboole_1, axiom,
% 2.19/2.39    (![A:$i,B:$i,C:$i]:
% 2.19/2.39     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 2.19/2.39       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 2.19/2.39  thf('37', plain,
% 2.19/2.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 2.19/2.39           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 2.19/2.39      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.19/2.39  thf('38', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1))
% 2.19/2.39           = (k4_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('sup+', [status(thm)], ['36', '37'])).
% 2.19/2.39  thf('39', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X0 @ X1)
% 2.19/2.39           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 2.19/2.39      inference('demod', [status(thm)], ['29', '38'])).
% 2.19/2.39  thf('40', plain,
% 2.19/2.39      (((k4_xboole_0 @ sk_B_1 @ sk_C_1)
% 2.19/2.39         = (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_C_1))),
% 2.19/2.39      inference('sup+', [status(thm)], ['1', '39'])).
% 2.19/2.39  thf('41', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 2.19/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.39  thf('42', plain,
% 2.19/2.39      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 2.19/2.39      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.19/2.39  thf(t4_xboole_0, axiom,
% 2.19/2.39    (![A:$i,B:$i]:
% 2.19/2.39     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.19/2.39            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.19/2.39       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.19/2.39            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.19/2.39  thf('43', plain,
% 2.19/2.39      (![X4 : $i, X6 : $i, X7 : $i]:
% 2.19/2.39         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 2.19/2.39          | ~ (r1_xboole_0 @ X4 @ X7))),
% 2.19/2.39      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.19/2.39  thf('44', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.19/2.39      inference('sup-', [status(thm)], ['42', '43'])).
% 2.19/2.39  thf('45', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))),
% 2.19/2.39      inference('sup-', [status(thm)], ['41', '44'])).
% 2.19/2.39  thf('46', plain,
% 2.19/2.39      (![X16 : $i, X17 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.19/2.39           = (k3_xboole_0 @ X16 @ X17))),
% 2.19/2.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.39  thf('47', plain,
% 2.19/2.39      (![X16 : $i, X17 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.19/2.39           = (k3_xboole_0 @ X16 @ X17))),
% 2.19/2.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.39  thf('48', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.19/2.39           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['46', '47'])).
% 2.19/2.39  thf('49', plain,
% 2.19/2.39      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0)
% 2.19/2.39         = (k3_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_C_1 @ sk_B_1)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['45', '48'])).
% 2.19/2.39  thf('50', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.19/2.39      inference('cnf', [status(esa)], [t3_boole])).
% 2.19/2.39  thf('51', plain,
% 2.19/2.39      (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_C_1 @ sk_B_1)))),
% 2.19/2.39      inference('demod', [status(thm)], ['49', '50'])).
% 2.19/2.39  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.19/2.39      inference('demod', [status(thm)], ['4', '5'])).
% 2.19/2.39  thf('53', plain,
% 2.19/2.39      (![X16 : $i, X17 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.19/2.39           = (k3_xboole_0 @ X16 @ X17))),
% 2.19/2.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.39  thf('54', plain,
% 2.19/2.39      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['52', '53'])).
% 2.19/2.39  thf('55', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.19/2.39      inference('cnf', [status(esa)], [t3_boole])).
% 2.19/2.39  thf('56', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 2.19/2.39      inference('demod', [status(thm)], ['54', '55'])).
% 2.19/2.39  thf('57', plain,
% 2.19/2.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 2.19/2.39           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 2.19/2.39      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.19/2.39  thf('58', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.19/2.39           = (k4_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('sup+', [status(thm)], ['56', '57'])).
% 2.19/2.39  thf('59', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 2.19/2.39      inference('demod', [status(thm)], ['51', '58'])).
% 2.19/2.39  thf('60', plain,
% 2.19/2.39      (![X16 : $i, X17 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.19/2.39           = (k3_xboole_0 @ X16 @ X17))),
% 2.19/2.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.39  thf('61', plain,
% 2.19/2.39      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 2.19/2.39           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.19/2.39  thf('62', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 2.19/2.39           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['60', '61'])).
% 2.19/2.39  thf('63', plain,
% 2.19/2.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 2.19/2.39           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 2.19/2.39      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.19/2.39  thf('64', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))
% 2.19/2.39           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 2.19/2.39      inference('demod', [status(thm)], ['62', '63'])).
% 2.19/2.39  thf('65', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['30', '31'])).
% 2.19/2.39  thf('66', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['64', '65'])).
% 2.19/2.39  thf('67', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.19/2.39           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['46', '47'])).
% 2.19/2.39  thf('68', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.19/2.39           = (k4_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('sup+', [status(thm)], ['56', '57'])).
% 2.19/2.39  thf('69', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.19/2.39           = (k4_xboole_0 @ X1 @ X0))),
% 2.19/2.39      inference('demod', [status(thm)], ['67', '68'])).
% 2.19/2.39  thf('70', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 2.19/2.39           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['66', '69'])).
% 2.19/2.39  thf('71', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.19/2.39      inference('cnf', [status(esa)], [t3_boole])).
% 2.19/2.39  thf('72', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('demod', [status(thm)], ['70', '71'])).
% 2.19/2.39  thf('73', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 2.19/2.39      inference('sup+', [status(thm)], ['59', '72'])).
% 2.19/2.39  thf('74', plain,
% 2.19/2.39      (((sk_B_1) = (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_C_1))),
% 2.19/2.39      inference('demod', [status(thm)], ['40', '73'])).
% 2.19/2.39  thf('75', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('demod', [status(thm)], ['25', '26'])).
% 2.19/2.39  thf('76', plain,
% 2.19/2.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 2.19/2.39           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 2.19/2.39      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.19/2.39  thf('77', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1))
% 2.19/2.39           = (k4_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('sup+', [status(thm)], ['75', '76'])).
% 2.19/2.39  thf('78', plain,
% 2.19/2.39      (![X4 : $i, X6 : $i, X7 : $i]:
% 2.19/2.39         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 2.19/2.39          | ~ (r1_xboole_0 @ X4 @ X7))),
% 2.19/2.39      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.19/2.39  thf('79', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.19/2.39         (~ (r2_hidden @ X3 @ (k4_xboole_0 @ X1 @ X0))
% 2.19/2.39          | ~ (r1_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X0)))),
% 2.19/2.39      inference('sup-', [status(thm)], ['77', '78'])).
% 2.19/2.39  thf('80', plain,
% 2.19/2.39      (![X0 : $i]:
% 2.19/2.39         (~ (r1_xboole_0 @ sk_A @ sk_B_1)
% 2.19/2.39          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_C_1)))),
% 2.19/2.39      inference('sup-', [status(thm)], ['74', '79'])).
% 2.19/2.39  thf('81', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 2.19/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.39  thf('82', plain,
% 2.19/2.39      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_C_1))),
% 2.19/2.39      inference('demod', [status(thm)], ['80', '81'])).
% 2.19/2.39  thf('83', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 2.19/2.39      inference('sup-', [status(thm)], ['0', '82'])).
% 2.19/2.39  thf('84', plain,
% 2.19/2.39      (![X16 : $i, X17 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.19/2.39           = (k3_xboole_0 @ X16 @ X17))),
% 2.19/2.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.39  thf('85', plain,
% 2.19/2.39      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 2.19/2.39      inference('sup+', [status(thm)], ['83', '84'])).
% 2.19/2.39  thf('86', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.19/2.39      inference('cnf', [status(esa)], [t3_boole])).
% 2.19/2.39  thf('87', plain,
% 2.19/2.39      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 2.19/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.39  thf('88', plain,
% 2.19/2.39      (![X14 : $i, X15 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 2.19/2.39      inference('cnf', [status(esa)], [t46_xboole_1])).
% 2.19/2.39  thf('89', plain,
% 2.19/2.39      (((k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['87', '88'])).
% 2.19/2.39  thf('90', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 2.19/2.39           = (k4_xboole_0 @ X2 @ 
% 2.19/2.39              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 2.19/2.39      inference('demod', [status(thm)], ['9', '10'])).
% 2.19/2.39  thf('91', plain,
% 2.19/2.39      (((k3_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_A) @ sk_B_1)
% 2.19/2.39         = (k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ k1_xboole_0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['89', '90'])).
% 2.19/2.39  thf('92', plain,
% 2.19/2.39      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.19/2.39  thf('93', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.19/2.39      inference('demod', [status(thm)], ['20', '21', '22', '27'])).
% 2.19/2.39  thf('94', plain,
% 2.19/2.39      (((k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_C_1 @ sk_A))
% 2.19/2.39         = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 2.19/2.39      inference('demod', [status(thm)], ['91', '92', '93'])).
% 2.19/2.39  thf('95', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))),
% 2.19/2.39      inference('sup-', [status(thm)], ['41', '44'])).
% 2.19/2.39  thf('96', plain,
% 2.19/2.39      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.19/2.39  thf('97', plain,
% 2.19/2.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 2.19/2.39           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 2.19/2.39      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.19/2.39  thf('98', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 2.19/2.39           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 2.19/2.39      inference('sup+', [status(thm)], ['96', '97'])).
% 2.19/2.39  thf('99', plain,
% 2.19/2.39      (![X0 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_C_1 @ X0))
% 2.19/2.39           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['95', '98'])).
% 2.19/2.39  thf('100', plain,
% 2.19/2.39      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.19/2.39  thf('101', plain,
% 2.19/2.39      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 2.19/2.39      inference('cnf', [status(esa)], [t2_boole])).
% 2.19/2.39  thf('102', plain,
% 2.19/2.39      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['100', '101'])).
% 2.19/2.39  thf('103', plain,
% 2.19/2.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 2.19/2.39           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 2.19/2.39      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.19/2.39  thf('104', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 2.19/2.39           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['102', '103'])).
% 2.19/2.39  thf('105', plain,
% 2.19/2.39      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['100', '101'])).
% 2.19/2.39  thf('106', plain,
% 2.19/2.39      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.19/2.39      inference('demod', [status(thm)], ['104', '105'])).
% 2.19/2.39  thf('107', plain,
% 2.19/2.39      (![X0 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_C_1 @ X0)) = (k1_xboole_0))),
% 2.19/2.39      inference('demod', [status(thm)], ['99', '106'])).
% 2.19/2.39  thf('108', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 2.19/2.39      inference('demod', [status(thm)], ['94', '107'])).
% 2.19/2.39  thf('109', plain,
% 2.19/2.39      (![X16 : $i, X17 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.19/2.39           = (k3_xboole_0 @ X16 @ X17))),
% 2.19/2.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.39  thf('110', plain,
% 2.19/2.39      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 2.19/2.39      inference('sup+', [status(thm)], ['108', '109'])).
% 2.19/2.39  thf('111', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.19/2.39      inference('cnf', [status(esa)], [t3_boole])).
% 2.19/2.39  thf('112', plain,
% 2.19/2.39      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.19/2.39  thf('113', plain, (((sk_C_1) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 2.19/2.39      inference('demod', [status(thm)], ['110', '111', '112'])).
% 2.19/2.39  thf('114', plain, (((sk_A) = (sk_C_1))),
% 2.19/2.39      inference('demod', [status(thm)], ['85', '86', '113'])).
% 2.19/2.39  thf('115', plain, (((sk_A) != (sk_C_1))),
% 2.19/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.39  thf('116', plain, ($false),
% 2.19/2.39      inference('simplify_reflect-', [status(thm)], ['114', '115'])).
% 2.19/2.39  
% 2.19/2.39  % SZS output end Refutation
% 2.19/2.39  
% 2.26/2.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
