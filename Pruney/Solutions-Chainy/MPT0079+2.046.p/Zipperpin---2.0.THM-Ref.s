%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lWWxH57cSe

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:03 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 840 expanded)
%              Number of leaves         :   25 ( 294 expanded)
%              Depth                    :   26
%              Number of atoms          : 1087 (7003 expanded)
%              Number of equality atoms :  133 ( 815 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_C_1 )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_B_1 ) @ sk_A )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','20','21','22','23'])).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_B_1 ) @ sk_A ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
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

thf('31',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','32'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
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
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('46',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['38','43','44','45'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k2_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ X0 )
      = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ X0 )
      = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['3','48'])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C_1 )
    = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k2_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58','61'])).

thf('63',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','62'])).

thf('64',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('70',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('76',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('78',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('79',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('81',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('83',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('85',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['67','76','77','78','85'])).

thf('87',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('89',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('91',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('95',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['67','76','77','78','85'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('98',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('100',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('102',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_C_1 )
    = ( k4_xboole_0 @ sk_D @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['67','76','77','78','85'])).

thf('106',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['98','99','104','105'])).

thf('107',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('108',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58','61'])).

thf('110',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('113',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['108','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('121',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['38','43','44','45'])).

thf('123',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['95','123'])).

thf('125',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['86','124'])).

thf('126',plain,(
    sk_C_1 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['125','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lWWxH57cSe
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:34:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 342 iterations in 0.141s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(t72_xboole_1, conjecture,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.39/0.59         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.39/0.59       ( ( C ) = ( B ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.39/0.59            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.39/0.59          ( ( C ) = ( B ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(commutativity_k2_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.59  thf(t40_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.39/0.59           = (k4_xboole_0 @ X14 @ X15))),
% 0.39/0.59      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.59  thf(t39_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (![X11 : $i, X12 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.39/0.59           = (k2_xboole_0 @ X11 @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.39/0.59           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['5', '6'])).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      (![X11 : $i, X12 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.39/0.59           = (k2_xboole_0 @ X11 @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X0 @ X1)
% 0.39/0.59           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (((k2_xboole_0 @ sk_D @ sk_C_1)
% 0.39/0.59         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['4', '9'])).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (((k2_xboole_0 @ sk_B_1 @ sk_A)
% 0.39/0.59         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.39/0.59           = (k4_xboole_0 @ X14 @ X15))),
% 0.39/0.59      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ 
% 0.39/0.59         (k2_xboole_0 @ sk_B_1 @ sk_A))
% 0.39/0.59         = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.59  thf(t1_boole, axiom,
% 0.39/0.59    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.59  thf('17', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.39/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.59  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.39/0.59           = (k4_xboole_0 @ X14 @ X15))),
% 0.39/0.59      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.39/0.59  thf(t41_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.59       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.39/0.59           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.39/0.59           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_B_1) @ sk_A)
% 0.39/0.59         = (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B_1) @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['15', '20', '21', '22', '23'])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X11 : $i, X12 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.39/0.59           = (k2_xboole_0 @ X11 @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      (((k2_xboole_0 @ sk_A @ 
% 0.39/0.59         (k4_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_B_1) @ sk_A))
% 0.39/0.59         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B_1)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['24', '25'])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      (![X11 : $i, X12 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.39/0.59           = (k2_xboole_0 @ X11 @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_B_1))
% 0.39/0.59         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B_1)))),
% 0.39/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.39/0.59  thf('29', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(t7_xboole_0, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.39/0.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.39/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.59  thf(t4_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.39/0.59          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.39/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.59  thf('33', plain, (((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['29', '32'])).
% 0.39/0.59  thf(t47_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (![X19 : $i, X20 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 0.39/0.59           = (k4_xboole_0 @ X19 @ X20))),
% 0.39/0.59      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['33', '34'])).
% 0.39/0.59  thf(t3_boole, axiom,
% 0.39/0.59    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.59  thf('36', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.59  thf('37', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.39/0.59      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_B_1))
% 0.39/0.59         = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['28', '37'])).
% 0.39/0.59  thf('39', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.59  thf(t48_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      (![X21 : $i, X22 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.39/0.59           = (k3_xboole_0 @ X21 @ X22))),
% 0.39/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.59  thf('41', plain,
% 0.39/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['39', '40'])).
% 0.39/0.59  thf(t2_boole, axiom,
% 0.39/0.59    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.59  thf('42', plain,
% 0.39/0.59      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.39/0.59  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.39/0.59  thf('44', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.59  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.39/0.59  thf('46', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['38', '43', '44', '45'])).
% 0.39/0.59  thf(t4_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.59       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.59  thf('47', plain,
% 0.39/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X25)
% 0.39/0.59           = (k2_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.39/0.59  thf('48', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ sk_A @ X0)
% 0.39/0.59           = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_D @ X0)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('49', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ sk_A @ X0)
% 0.39/0.59           = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_D)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['3', '48'])).
% 0.39/0.59  thf('50', plain,
% 0.39/0.59      (((k2_xboole_0 @ sk_A @ sk_C_1)
% 0.39/0.59         = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['2', '49'])).
% 0.39/0.59  thf('51', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.59  thf('52', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X0 @ X1)
% 0.39/0.59           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.59  thf('53', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X0 @ X1)
% 0.39/0.59           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.59  thf('54', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1)
% 0.39/0.59           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['52', '53'])).
% 0.39/0.59  thf('55', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.59  thf('56', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X0 @ X1)
% 0.39/0.59           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.59  thf('57', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X1 @ X0)
% 0.39/0.59           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.39/0.59  thf('58', plain,
% 0.39/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X25)
% 0.39/0.59           = (k2_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.39/0.59  thf('59', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.59  thf('60', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X0 @ X1)
% 0.39/0.59           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.59  thf('61', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X1 @ X0)
% 0.39/0.59           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['59', '60'])).
% 0.39/0.59  thf('62', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X1 @ X0)
% 0.39/0.59           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['57', '58', '61'])).
% 0.39/0.59  thf('63', plain,
% 0.39/0.59      (((k2_xboole_0 @ sk_C_1 @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['50', '51', '62'])).
% 0.39/0.59  thf('64', plain,
% 0.39/0.59      (![X11 : $i, X12 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.39/0.59           = (k2_xboole_0 @ X11 @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.59  thf('65', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.39/0.59           = (k4_xboole_0 @ X14 @ X15))),
% 0.39/0.59      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.59  thf('66', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.39/0.59           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['64', '65'])).
% 0.39/0.59  thf('67', plain,
% 0.39/0.59      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ 
% 0.39/0.59         (k4_xboole_0 @ sk_A @ sk_C_1))
% 0.39/0.59         = (k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_C_1)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['63', '66'])).
% 0.39/0.59  thf('68', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(symmetry_r1_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.39/0.59  thf('69', plain,
% 0.39/0.59      (![X2 : $i, X3 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.39/0.59  thf('70', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.39/0.59      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.59  thf('71', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.59  thf('72', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['70', '71'])).
% 0.39/0.59  thf('73', plain,
% 0.39/0.59      (![X19 : $i, X20 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 0.39/0.59           = (k4_xboole_0 @ X19 @ X20))),
% 0.39/0.59      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.39/0.59  thf('74', plain,
% 0.39/0.59      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['72', '73'])).
% 0.39/0.59  thf('75', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.59  thf('76', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.39/0.59      inference('demod', [status(thm)], ['74', '75'])).
% 0.39/0.59  thf('77', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.39/0.59           = (k4_xboole_0 @ X14 @ X15))),
% 0.39/0.59      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.59  thf('78', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.39/0.59      inference('demod', [status(thm)], ['74', '75'])).
% 0.39/0.59  thf('79', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('80', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.59  thf('81', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['79', '80'])).
% 0.39/0.59  thf('82', plain,
% 0.39/0.59      (![X19 : $i, X20 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 0.39/0.59           = (k4_xboole_0 @ X19 @ X20))),
% 0.39/0.59      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.39/0.59  thf('83', plain,
% 0.39/0.59      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.39/0.59      inference('sup+', [status(thm)], ['81', '82'])).
% 0.39/0.59  thf('84', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.59  thf('85', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['83', '84'])).
% 0.39/0.59  thf('86', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.39/0.59      inference('demod', [status(thm)], ['67', '76', '77', '78', '85'])).
% 0.39/0.59  thf('87', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('88', plain,
% 0.39/0.59      (![X2 : $i, X3 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.39/0.59  thf('89', plain, ((r1_xboole_0 @ sk_B_1 @ sk_D)),
% 0.39/0.59      inference('sup-', [status(thm)], ['87', '88'])).
% 0.39/0.59  thf('90', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.59  thf('91', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['89', '90'])).
% 0.39/0.59  thf('92', plain,
% 0.39/0.59      (![X19 : $i, X20 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 0.39/0.59           = (k4_xboole_0 @ X19 @ X20))),
% 0.39/0.59      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.39/0.59  thf('93', plain,
% 0.39/0.59      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 0.39/0.59      inference('sup+', [status(thm)], ['91', '92'])).
% 0.39/0.59  thf('94', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.59  thf('95', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['93', '94'])).
% 0.39/0.59  thf('96', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.39/0.59      inference('demod', [status(thm)], ['67', '76', '77', '78', '85'])).
% 0.39/0.59  thf('97', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.39/0.59           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['64', '65'])).
% 0.39/0.59  thf('98', plain,
% 0.39/0.59      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_C_1)
% 0.39/0.59         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['96', '97'])).
% 0.39/0.59  thf('99', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.59  thf('100', plain,
% 0.39/0.59      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.59  thf('101', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.59  thf('102', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.39/0.59           = (k4_xboole_0 @ X14 @ X15))),
% 0.39/0.59      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.59  thf('103', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.39/0.59           = (k4_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['101', '102'])).
% 0.39/0.59  thf('104', plain,
% 0.39/0.59      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_C_1)
% 0.39/0.59         = (k4_xboole_0 @ sk_D @ sk_C_1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['100', '103'])).
% 0.39/0.59  thf('105', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.39/0.59      inference('demod', [status(thm)], ['67', '76', '77', '78', '85'])).
% 0.39/0.59  thf('106', plain,
% 0.39/0.59      (((k4_xboole_0 @ sk_D @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.39/0.59      inference('demod', [status(thm)], ['98', '99', '104', '105'])).
% 0.39/0.59  thf('107', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.39/0.59      inference('demod', [status(thm)], ['74', '75'])).
% 0.39/0.59  thf('108', plain, (((k4_xboole_0 @ sk_D @ sk_C_1) = (sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['106', '107'])).
% 0.39/0.59  thf('109', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X1 @ X0)
% 0.39/0.59           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['57', '58', '61'])).
% 0.39/0.59  thf('110', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.39/0.59           = (k4_xboole_0 @ X14 @ X15))),
% 0.39/0.59      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.59  thf('111', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.39/0.59           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['109', '110'])).
% 0.39/0.59  thf('112', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.39/0.59  thf('113', plain,
% 0.39/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.39/0.59           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.59  thf('114', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.39/0.59      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.39/0.59  thf('115', plain,
% 0.39/0.59      (![X11 : $i, X12 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.39/0.59           = (k2_xboole_0 @ X11 @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.59  thf('116', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.39/0.59           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['114', '115'])).
% 0.39/0.59  thf('117', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.39/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.59  thf('118', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['116', '117'])).
% 0.39/0.59  thf('119', plain, (((sk_D) = (k2_xboole_0 @ sk_D @ sk_A))),
% 0.39/0.59      inference('sup+', [status(thm)], ['108', '118'])).
% 0.39/0.59  thf('120', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.59  thf('121', plain, (((sk_D) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['119', '120'])).
% 0.39/0.59  thf('122', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['38', '43', '44', '45'])).
% 0.39/0.59  thf('123', plain, (((sk_A) = (sk_D))),
% 0.39/0.59      inference('sup+', [status(thm)], ['121', '122'])).
% 0.39/0.59  thf('124', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['95', '123'])).
% 0.39/0.59  thf('125', plain, (((sk_B_1) = (sk_C_1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['86', '124'])).
% 0.39/0.59  thf('126', plain, (((sk_C_1) != (sk_B_1))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('127', plain, ($false),
% 0.39/0.59      inference('simplify_reflect-', [status(thm)], ['125', '126'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
