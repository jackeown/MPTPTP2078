%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bjcc9Wb7xO

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:00 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  173 (2290 expanded)
%              Number of leaves         :   25 ( 797 expanded)
%              Depth                    :   26
%              Number of atoms          : 1241 (17163 expanded)
%              Number of equality atoms :  159 (2289 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17','18','19','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','29'])).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('31',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_C_1 @ sk_D ) )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_D )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('42',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_D ) @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('46',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_D ) @ sk_B_1 ) @ sk_A )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ sk_B_1 ) @ sk_A )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['30','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17','18','19','28'])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('53',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('54',plain,(
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

thf('55',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['48','51','52','65'])).

thf('67',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('68',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('71',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('73',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('74',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k2_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ X0 )
      = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k2_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ sk_A ) )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['71','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('81',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('83',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('88',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('92',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('94',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('95',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('96',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('97',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('99',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['85','92','93','94','99'])).

thf('101',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['57','58'])).

thf('102',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('103',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('105',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['85','92','93','94','99'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('108',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('110',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('112',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_C_1 )
    = ( k4_xboole_0 @ sk_D @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['110','113'])).

thf('115',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['85','92','93','94','99'])).

thf('116',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['108','109','114','115'])).

thf('117',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('118',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('125',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','29'])).

thf('129',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['118','130'])).

thf('132',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('133',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_D ) @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['48','51','52','65'])).

thf('135',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('136',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('138',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('139',plain,
    ( sk_D
    = ( k3_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('142',plain,(
    sk_D = sk_A ),
    inference(demod,[status(thm)],['133','139','140','141'])).

thf('143',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','142'])).

thf('144',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['100','143'])).

thf('145',plain,(
    sk_C_1 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bjcc9Wb7xO
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:00:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.51/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.74  % Solved by: fo/fo7.sh
% 0.51/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.74  % done 608 iterations in 0.281s
% 0.51/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.74  % SZS output start Refutation
% 0.51/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.74  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.51/0.74  thf(sk_D_type, type, sk_D: $i).
% 0.51/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.51/0.74  thf(sk_B_type, type, sk_B: $i > $i).
% 0.51/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.74  thf(t3_boole, axiom,
% 0.51/0.74    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.51/0.74  thf('0', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.51/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.74  thf(t48_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.51/0.74  thf('1', plain,
% 0.51/0.74      (![X20 : $i, X21 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.51/0.74           = (k3_xboole_0 @ X20 @ X21))),
% 0.51/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.51/0.74  thf('2', plain,
% 0.51/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['0', '1'])).
% 0.51/0.74  thf(t47_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.51/0.74  thf('3', plain,
% 0.51/0.74      (![X18 : $i, X19 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 0.51/0.74           = (k4_xboole_0 @ X18 @ X19))),
% 0.51/0.74      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.51/0.74  thf('4', plain,
% 0.51/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['0', '1'])).
% 0.51/0.74  thf(commutativity_k2_xboole_0, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.51/0.74  thf('5', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.74  thf(t1_boole, axiom,
% 0.51/0.74    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.51/0.74  thf('6', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.51/0.74      inference('cnf', [status(esa)], [t1_boole])).
% 0.51/0.74  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['5', '6'])).
% 0.51/0.74  thf(t40_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.51/0.74  thf('8', plain,
% 0.51/0.74      (![X13 : $i, X14 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.51/0.74           = (k4_xboole_0 @ X13 @ X14))),
% 0.51/0.74      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.51/0.74  thf('9', plain,
% 0.51/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['7', '8'])).
% 0.51/0.74  thf('10', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['4', '9'])).
% 0.51/0.74  thf('11', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k3_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.51/0.74           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['3', '10'])).
% 0.51/0.74  thf(commutativity_k3_xboole_0, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.51/0.74  thf('12', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.74  thf('13', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['4', '9'])).
% 0.51/0.74  thf('14', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.51/0.74           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.51/0.74  thf(t51_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.51/0.74       ( A ) ))).
% 0.51/0.74  thf('15', plain,
% 0.51/0.74      (![X25 : $i, X26 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ (k4_xboole_0 @ X25 @ X26))
% 0.51/0.74           = (X25))),
% 0.51/0.74      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.51/0.74  thf('16', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.51/0.74           (k4_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 0.51/0.74           = (k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['14', '15'])).
% 0.51/0.74  thf('17', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['4', '9'])).
% 0.51/0.74  thf('18', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.74  thf('19', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.51/0.74           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.51/0.74  thf('20', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['5', '6'])).
% 0.51/0.74  thf('21', plain,
% 0.51/0.74      (![X13 : $i, X14 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.51/0.74           = (k4_xboole_0 @ X13 @ X14))),
% 0.51/0.74      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.51/0.74  thf(t39_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.51/0.74  thf('22', plain,
% 0.51/0.74      (![X10 : $i, X11 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.51/0.74           = (k2_xboole_0 @ X10 @ X11))),
% 0.51/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.51/0.74  thf('23', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.51/0.74           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['21', '22'])).
% 0.51/0.74  thf('24', plain,
% 0.51/0.74      (![X10 : $i, X11 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.51/0.74           = (k2_xboole_0 @ X10 @ X11))),
% 0.51/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.51/0.74  thf('25', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X0 @ X1)
% 0.51/0.74           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.51/0.74      inference('demod', [status(thm)], ['23', '24'])).
% 0.51/0.74  thf('26', plain,
% 0.51/0.74      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['20', '25'])).
% 0.51/0.74  thf('27', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.51/0.74      inference('cnf', [status(esa)], [t1_boole])).
% 0.51/0.74  thf('28', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.51/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.51/0.74  thf('29', plain,
% 0.51/0.74      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['16', '17', '18', '19', '28'])).
% 0.51/0.74  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['2', '29'])).
% 0.51/0.74  thf(t72_xboole_1, conjecture,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.51/0.74         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.51/0.74       ( ( C ) = ( B ) ) ))).
% 0.51/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.51/0.74            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.51/0.74          ( ( C ) = ( B ) ) ) )),
% 0.51/0.74    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.51/0.74  thf('31', plain,
% 0.51/0.74      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('32', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.74  thf('33', plain,
% 0.51/0.74      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.51/0.74      inference('demod', [status(thm)], ['31', '32'])).
% 0.51/0.74  thf('34', plain,
% 0.51/0.74      (![X13 : $i, X14 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.51/0.74           = (k4_xboole_0 @ X13 @ X14))),
% 0.51/0.74      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.51/0.74  thf('35', plain,
% 0.51/0.74      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D)
% 0.51/0.74         = (k4_xboole_0 @ sk_C_1 @ sk_D))),
% 0.51/0.74      inference('sup+', [status(thm)], ['33', '34'])).
% 0.51/0.74  thf('36', plain,
% 0.51/0.74      (![X10 : $i, X11 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.51/0.74           = (k2_xboole_0 @ X10 @ X11))),
% 0.51/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.51/0.74  thf('37', plain,
% 0.51/0.74      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_C_1 @ sk_D))
% 0.51/0.74         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['35', '36'])).
% 0.51/0.74  thf('38', plain,
% 0.51/0.74      (![X10 : $i, X11 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.51/0.74           = (k2_xboole_0 @ X10 @ X11))),
% 0.51/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.51/0.74  thf('39', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.74  thf('40', plain,
% 0.51/0.74      (((k2_xboole_0 @ sk_C_1 @ sk_D)
% 0.51/0.74         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.51/0.74      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.51/0.74  thf('41', plain,
% 0.51/0.74      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.51/0.74      inference('demod', [status(thm)], ['31', '32'])).
% 0.51/0.74  thf('42', plain,
% 0.51/0.74      (((k2_xboole_0 @ sk_B_1 @ sk_A)
% 0.51/0.74         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.51/0.74      inference('demod', [status(thm)], ['40', '41'])).
% 0.51/0.74  thf(t41_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.51/0.74       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.51/0.74  thf('43', plain,
% 0.51/0.74      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.51/0.74           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.51/0.74  thf('44', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_D) @ 
% 0.51/0.74           (k2_xboole_0 @ sk_B_1 @ sk_A))
% 0.51/0.74           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['42', '43'])).
% 0.51/0.74  thf('45', plain,
% 0.51/0.74      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.51/0.74           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.51/0.74  thf('46', plain,
% 0.51/0.74      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.51/0.74           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.51/0.74  thf('47', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_D) @ sk_B_1) @ 
% 0.51/0.74           sk_A) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B_1) @ sk_A))),
% 0.51/0.74      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.51/0.74  thf('48', plain,
% 0.51/0.74      (((k4_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ sk_B_1) @ sk_A)
% 0.51/0.74         = (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B_1) @ sk_A))),
% 0.51/0.74      inference('sup+', [status(thm)], ['30', '47'])).
% 0.51/0.74  thf('49', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['4', '9'])).
% 0.51/0.74  thf('50', plain,
% 0.51/0.74      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['16', '17', '18', '19', '28'])).
% 0.51/0.74  thf('51', plain,
% 0.51/0.74      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.74      inference('demod', [status(thm)], ['49', '50'])).
% 0.51/0.74  thf('52', plain,
% 0.51/0.74      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.74      inference('demod', [status(thm)], ['49', '50'])).
% 0.51/0.74  thf('53', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(t7_xboole_0, axiom,
% 0.51/0.74    (![A:$i]:
% 0.51/0.74     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.51/0.74          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.51/0.74  thf('54', plain,
% 0.51/0.74      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.51/0.74      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.51/0.74  thf(t4_xboole_0, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.51/0.74            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.51/0.74       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.51/0.74            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.51/0.74  thf('55', plain,
% 0.51/0.74      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.51/0.74         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.51/0.74          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.51/0.74      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.51/0.74  thf('56', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['54', '55'])).
% 0.51/0.74  thf('57', plain, (((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['53', '56'])).
% 0.51/0.74  thf('58', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.74  thf('59', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['57', '58'])).
% 0.51/0.74  thf('60', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.74  thf('61', plain,
% 0.51/0.74      (![X18 : $i, X19 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 0.51/0.74           = (k4_xboole_0 @ X18 @ X19))),
% 0.51/0.74      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.51/0.74  thf('62', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.51/0.74           = (k4_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('sup+', [status(thm)], ['60', '61'])).
% 0.51/0.74  thf('63', plain,
% 0.51/0.74      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.51/0.74      inference('sup+', [status(thm)], ['59', '62'])).
% 0.51/0.74  thf('64', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.51/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.74  thf('65', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.51/0.74      inference('demod', [status(thm)], ['63', '64'])).
% 0.51/0.74  thf('66', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 0.51/0.74      inference('demod', [status(thm)], ['48', '51', '52', '65'])).
% 0.51/0.74  thf('67', plain,
% 0.51/0.74      (![X10 : $i, X11 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.51/0.74           = (k2_xboole_0 @ X10 @ X11))),
% 0.51/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.51/0.74  thf('68', plain,
% 0.51/0.74      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.51/0.74      inference('sup+', [status(thm)], ['66', '67'])).
% 0.51/0.74  thf('69', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.74  thf('70', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['5', '6'])).
% 0.51/0.74  thf('71', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.51/0.74      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.51/0.74  thf('72', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.74  thf('73', plain,
% 0.51/0.74      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.51/0.74      inference('demod', [status(thm)], ['31', '32'])).
% 0.51/0.74  thf(t4_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.51/0.74       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.51/0.74  thf('74', plain,
% 0.51/0.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ (k2_xboole_0 @ X22 @ X23) @ X24)
% 0.51/0.74           = (k2_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.51/0.74  thf('75', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ X0)
% 0.51/0.74           = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_D @ X0)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['73', '74'])).
% 0.51/0.74  thf('76', plain,
% 0.51/0.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ (k2_xboole_0 @ X22 @ X23) @ X24)
% 0.51/0.74           = (k2_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.51/0.74  thf('77', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_A @ X0))
% 0.51/0.74           = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_D @ X0)))),
% 0.51/0.74      inference('demod', [status(thm)], ['75', '76'])).
% 0.51/0.74  thf('78', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_A @ X0))
% 0.51/0.74           = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ X0 @ sk_D)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['72', '77'])).
% 0.51/0.74  thf('79', plain,
% 0.51/0.74      (((k2_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_A @ sk_A))
% 0.51/0.74         = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 0.51/0.74      inference('sup+', [status(thm)], ['71', '78'])).
% 0.51/0.74  thf('80', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.51/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.51/0.74  thf('81', plain,
% 0.51/0.74      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 0.51/0.74      inference('demod', [status(thm)], ['79', '80'])).
% 0.51/0.74  thf('82', plain,
% 0.51/0.74      (![X10 : $i, X11 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.51/0.74           = (k2_xboole_0 @ X10 @ X11))),
% 0.51/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.51/0.74  thf('83', plain,
% 0.51/0.74      (![X13 : $i, X14 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.51/0.74           = (k4_xboole_0 @ X13 @ X14))),
% 0.51/0.74      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.51/0.74  thf('84', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.51/0.74           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['82', '83'])).
% 0.51/0.74  thf('85', plain,
% 0.51/0.74      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ 
% 0.51/0.74         (k4_xboole_0 @ sk_A @ sk_C_1))
% 0.51/0.74         = (k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_C_1)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['81', '84'])).
% 0.51/0.74  thf('86', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('87', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['54', '55'])).
% 0.51/0.74  thf('88', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['86', '87'])).
% 0.51/0.74  thf('89', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.51/0.74           = (k4_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('sup+', [status(thm)], ['60', '61'])).
% 0.51/0.74  thf('90', plain,
% 0.51/0.74      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.51/0.74      inference('sup+', [status(thm)], ['88', '89'])).
% 0.51/0.74  thf('91', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.51/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.74  thf('92', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.51/0.74      inference('demod', [status(thm)], ['90', '91'])).
% 0.51/0.74  thf('93', plain,
% 0.51/0.74      (![X13 : $i, X14 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.51/0.74           = (k4_xboole_0 @ X13 @ X14))),
% 0.51/0.74      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.51/0.74  thf('94', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.51/0.74      inference('demod', [status(thm)], ['90', '91'])).
% 0.51/0.74  thf('95', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['86', '87'])).
% 0.51/0.74  thf('96', plain,
% 0.51/0.74      (![X18 : $i, X19 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 0.51/0.74           = (k4_xboole_0 @ X18 @ X19))),
% 0.51/0.74      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.51/0.74  thf('97', plain,
% 0.51/0.74      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.51/0.74      inference('sup+', [status(thm)], ['95', '96'])).
% 0.51/0.74  thf('98', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.51/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.74  thf('99', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.51/0.74      inference('demod', [status(thm)], ['97', '98'])).
% 0.51/0.74  thf('100', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.51/0.74      inference('demod', [status(thm)], ['85', '92', '93', '94', '99'])).
% 0.51/0.74  thf('101', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['57', '58'])).
% 0.51/0.74  thf('102', plain,
% 0.51/0.74      (![X18 : $i, X19 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 0.51/0.74           = (k4_xboole_0 @ X18 @ X19))),
% 0.51/0.74      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.51/0.74  thf('103', plain,
% 0.51/0.74      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 0.51/0.74      inference('sup+', [status(thm)], ['101', '102'])).
% 0.51/0.74  thf('104', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.51/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.74  thf('105', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 0.51/0.74      inference('demod', [status(thm)], ['103', '104'])).
% 0.51/0.74  thf('106', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.51/0.74      inference('demod', [status(thm)], ['85', '92', '93', '94', '99'])).
% 0.51/0.74  thf('107', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.51/0.74           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['82', '83'])).
% 0.51/0.74  thf('108', plain,
% 0.51/0.74      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_C_1)
% 0.51/0.74         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['106', '107'])).
% 0.51/0.74  thf('109', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.74  thf('110', plain,
% 0.51/0.74      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.51/0.74      inference('demod', [status(thm)], ['31', '32'])).
% 0.51/0.74  thf('111', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.74  thf('112', plain,
% 0.51/0.74      (![X13 : $i, X14 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.51/0.74           = (k4_xboole_0 @ X13 @ X14))),
% 0.51/0.74      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.51/0.74  thf('113', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.51/0.74           = (k4_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('sup+', [status(thm)], ['111', '112'])).
% 0.51/0.74  thf('114', plain,
% 0.51/0.74      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_C_1)
% 0.51/0.74         = (k4_xboole_0 @ sk_D @ sk_C_1))),
% 0.51/0.74      inference('sup+', [status(thm)], ['110', '113'])).
% 0.51/0.74  thf('115', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.51/0.74      inference('demod', [status(thm)], ['85', '92', '93', '94', '99'])).
% 0.51/0.74  thf('116', plain,
% 0.51/0.74      (((k4_xboole_0 @ sk_D @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.51/0.74      inference('demod', [status(thm)], ['108', '109', '114', '115'])).
% 0.51/0.74  thf('117', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.51/0.74      inference('demod', [status(thm)], ['90', '91'])).
% 0.51/0.74  thf('118', plain, (((k4_xboole_0 @ sk_D @ sk_C_1) = (sk_A))),
% 0.51/0.74      inference('demod', [status(thm)], ['116', '117'])).
% 0.51/0.74  thf('119', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.74  thf('120', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X0 @ X1)
% 0.51/0.74           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.51/0.74      inference('demod', [status(thm)], ['23', '24'])).
% 0.51/0.74  thf('121', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X1 @ X0)
% 0.51/0.74           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['119', '120'])).
% 0.51/0.74  thf('122', plain,
% 0.51/0.74      (![X13 : $i, X14 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.51/0.74           = (k4_xboole_0 @ X13 @ X14))),
% 0.51/0.74      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.51/0.74  thf('123', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.51/0.74           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['121', '122'])).
% 0.51/0.74  thf('124', plain,
% 0.51/0.74      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.51/0.74           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.51/0.74  thf('125', plain,
% 0.51/0.74      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.51/0.74           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.51/0.74  thf('126', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 0.51/0.74           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0))),
% 0.51/0.74      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.51/0.74  thf('127', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.51/0.74           = (k4_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('sup+', [status(thm)], ['111', '112'])).
% 0.51/0.74  thf('128', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['2', '29'])).
% 0.51/0.74  thf('129', plain,
% 0.51/0.74      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.74      inference('demod', [status(thm)], ['49', '50'])).
% 0.51/0.74  thf('130', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.51/0.74  thf('131', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['118', '130'])).
% 0.51/0.74  thf('132', plain,
% 0.51/0.74      (![X25 : $i, X26 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ (k4_xboole_0 @ X25 @ X26))
% 0.51/0.74           = (X25))),
% 0.51/0.74      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.51/0.74  thf('133', plain,
% 0.51/0.74      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_D) @ k1_xboole_0) = (sk_A))),
% 0.51/0.74      inference('sup+', [status(thm)], ['131', '132'])).
% 0.51/0.74  thf('134', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 0.51/0.74      inference('demod', [status(thm)], ['48', '51', '52', '65'])).
% 0.51/0.74  thf('135', plain,
% 0.51/0.74      (![X20 : $i, X21 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.51/0.74           = (k3_xboole_0 @ X20 @ X21))),
% 0.51/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.51/0.74  thf('136', plain,
% 0.51/0.74      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k3_xboole_0 @ sk_D @ sk_A))),
% 0.51/0.74      inference('sup+', [status(thm)], ['134', '135'])).
% 0.51/0.74  thf('137', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.51/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.74  thf('138', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.74  thf('139', plain, (((sk_D) = (k3_xboole_0 @ sk_A @ sk_D))),
% 0.51/0.74      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.51/0.74  thf('140', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.74  thf('141', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['5', '6'])).
% 0.51/0.74  thf('142', plain, (((sk_D) = (sk_A))),
% 0.51/0.74      inference('demod', [status(thm)], ['133', '139', '140', '141'])).
% 0.51/0.74  thf('143', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 0.51/0.74      inference('demod', [status(thm)], ['105', '142'])).
% 0.51/0.74  thf('144', plain, (((sk_B_1) = (sk_C_1))),
% 0.51/0.74      inference('sup+', [status(thm)], ['100', '143'])).
% 0.51/0.74  thf('145', plain, (((sk_C_1) != (sk_B_1))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('146', plain, ($false),
% 0.51/0.74      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.51/0.74  
% 0.51/0.74  % SZS output end Refutation
% 0.51/0.74  
% 0.51/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
