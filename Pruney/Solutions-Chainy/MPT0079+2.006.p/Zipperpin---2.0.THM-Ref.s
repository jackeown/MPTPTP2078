%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y4otp2iqFJ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:57 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 600 expanded)
%              Number of leaves         :   24 ( 203 expanded)
%              Depth                    :   19
%              Number of atoms          : 1068 (4687 expanded)
%              Number of equality atoms :  126 ( 506 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_D ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
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

thf('16',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['13','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ sk_D ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('35',plain,(
    r1_tarski @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_D ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('53',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['40','53'])).

thf('55',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,
    ( sk_D
    = ( k3_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['32','61'])).

thf('63',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('65',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('67',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_D @ X0 ) )
      = ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('73',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['75','79'])).

thf('81',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','82'])).

thf('84',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('87',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('88',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('89',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['85','86','87','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_D @ X0 ) )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','97'])).

thf('99',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['32','61'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ X0 @ sk_A ) )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','100'])).

thf('102',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['63','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ X0 @ sk_A ) )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','100'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('105',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('107',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('109',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('111',plain,(
    r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('113',plain,(
    r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('115',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','17'])).

thf('121',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('122',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('124',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['119','124'])).

thf('126',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('128',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('130',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('132',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('133',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    sk_B_1 = sk_C_1 ),
    inference(demod,[status(thm)],['107','108','133'])).

thf('135',plain,(
    sk_C_1 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['134','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y4otp2iqFJ
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:28:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.30/1.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.30/1.46  % Solved by: fo/fo7.sh
% 1.30/1.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.30/1.46  % done 2822 iterations in 1.003s
% 1.30/1.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.30/1.46  % SZS output start Refutation
% 1.30/1.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.30/1.46  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.30/1.46  thf(sk_A_type, type, sk_A: $i).
% 1.30/1.46  thf(sk_B_type, type, sk_B: $i > $i).
% 1.30/1.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.30/1.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.30/1.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.30/1.46  thf(sk_D_type, type, sk_D: $i).
% 1.30/1.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.30/1.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.30/1.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.30/1.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.30/1.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.30/1.46  thf(t72_xboole_1, conjecture,
% 1.30/1.46    (![A:$i,B:$i,C:$i,D:$i]:
% 1.30/1.46     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.30/1.46         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.30/1.46       ( ( C ) = ( B ) ) ))).
% 1.30/1.46  thf(zf_stmt_0, negated_conjecture,
% 1.30/1.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.30/1.46        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.30/1.46            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.30/1.46          ( ( C ) = ( B ) ) ) )),
% 1.30/1.46    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 1.30/1.46  thf('0', plain,
% 1.30/1.46      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 1.30/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.46  thf(commutativity_k2_xboole_0, axiom,
% 1.30/1.46    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.30/1.46  thf('1', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.30/1.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.30/1.46  thf('2', plain,
% 1.30/1.46      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 1.30/1.46      inference('demod', [status(thm)], ['0', '1'])).
% 1.30/1.46  thf('3', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.30/1.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.30/1.46  thf(t7_xboole_1, axiom,
% 1.30/1.46    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.30/1.46  thf('4', plain,
% 1.30/1.46      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 1.30/1.46      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.30/1.46  thf('5', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.30/1.46      inference('sup+', [status(thm)], ['3', '4'])).
% 1.30/1.46  thf(l32_xboole_1, axiom,
% 1.30/1.46    (![A:$i,B:$i]:
% 1.30/1.46     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.30/1.46  thf('6', plain,
% 1.30/1.46      (![X9 : $i, X11 : $i]:
% 1.30/1.46         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 1.30/1.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.30/1.46  thf('7', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['5', '6'])).
% 1.30/1.46  thf('8', plain,
% 1.30/1.46      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 1.30/1.46      inference('demod', [status(thm)], ['0', '1'])).
% 1.30/1.46  thf(t41_xboole_1, axiom,
% 1.30/1.46    (![A:$i,B:$i,C:$i]:
% 1.30/1.46     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.30/1.46       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.30/1.46  thf('9', plain,
% 1.30/1.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.30/1.46           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.30/1.46      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.30/1.46  thf('10', plain,
% 1.30/1.46      (![X9 : $i, X10 : $i]:
% 1.30/1.46         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 1.30/1.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.30/1.46  thf('11', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.46         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.30/1.46          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['9', '10'])).
% 1.30/1.46  thf('12', plain,
% 1.30/1.46      (![X0 : $i]:
% 1.30/1.46         (((k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_A)) != (k1_xboole_0))
% 1.30/1.46          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D))),
% 1.30/1.46      inference('sup-', [status(thm)], ['8', '11'])).
% 1.30/1.46  thf('13', plain,
% 1.30/1.46      ((((k1_xboole_0) != (k1_xboole_0))
% 1.30/1.46        | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_D))),
% 1.30/1.46      inference('sup-', [status(thm)], ['7', '12'])).
% 1.30/1.46  thf('14', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 1.30/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.46  thf(t7_xboole_0, axiom,
% 1.30/1.46    (![A:$i]:
% 1.30/1.46     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.30/1.46          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.30/1.46  thf('15', plain,
% 1.30/1.46      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 1.30/1.46      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.30/1.46  thf(t4_xboole_0, axiom,
% 1.30/1.46    (![A:$i,B:$i]:
% 1.30/1.46     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.30/1.46            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.30/1.46       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.30/1.46            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.30/1.46  thf('16', plain,
% 1.30/1.46      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.30/1.46         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 1.30/1.46          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.30/1.46      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.30/1.46  thf('17', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]:
% 1.30/1.46         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['15', '16'])).
% 1.30/1.46  thf('18', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['14', '17'])).
% 1.30/1.46  thf(commutativity_k3_xboole_0, axiom,
% 1.30/1.46    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.30/1.46  thf('19', plain,
% 1.30/1.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.30/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.30/1.46  thf(t47_xboole_1, axiom,
% 1.30/1.46    (![A:$i,B:$i]:
% 1.30/1.46     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.30/1.46  thf('20', plain,
% 1.30/1.46      (![X16 : $i, X17 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17))
% 1.30/1.46           = (k4_xboole_0 @ X16 @ X17))),
% 1.30/1.46      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.30/1.46  thf('21', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.30/1.46           = (k4_xboole_0 @ X0 @ X1))),
% 1.30/1.46      inference('sup+', [status(thm)], ['19', '20'])).
% 1.30/1.46  thf('22', plain,
% 1.30/1.46      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.30/1.46      inference('sup+', [status(thm)], ['18', '21'])).
% 1.30/1.46  thf(t3_boole, axiom,
% 1.30/1.46    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.30/1.46  thf('23', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.30/1.46      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.46  thf('24', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.30/1.46      inference('demod', [status(thm)], ['22', '23'])).
% 1.30/1.46  thf('25', plain,
% 1.30/1.46      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_D))),
% 1.30/1.46      inference('demod', [status(thm)], ['13', '24'])).
% 1.30/1.46  thf('26', plain, ((r1_tarski @ sk_A @ sk_D)),
% 1.30/1.46      inference('simplify', [status(thm)], ['25'])).
% 1.30/1.46  thf('27', plain,
% 1.30/1.46      (![X9 : $i, X11 : $i]:
% 1.30/1.46         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 1.30/1.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.30/1.46  thf('28', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['26', '27'])).
% 1.30/1.46  thf(t48_xboole_1, axiom,
% 1.30/1.46    (![A:$i,B:$i]:
% 1.30/1.46     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.30/1.46  thf('29', plain,
% 1.30/1.46      (![X18 : $i, X19 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.30/1.46           = (k3_xboole_0 @ X18 @ X19))),
% 1.30/1.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.46  thf('30', plain,
% 1.30/1.46      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_D))),
% 1.30/1.46      inference('sup+', [status(thm)], ['28', '29'])).
% 1.30/1.46  thf('31', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.30/1.46      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.46  thf('32', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_D))),
% 1.30/1.46      inference('demod', [status(thm)], ['30', '31'])).
% 1.30/1.46  thf('33', plain,
% 1.30/1.46      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 1.30/1.46      inference('demod', [status(thm)], ['0', '1'])).
% 1.30/1.46  thf('34', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.30/1.46      inference('sup+', [status(thm)], ['3', '4'])).
% 1.30/1.46  thf('35', plain, ((r1_tarski @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 1.30/1.46      inference('sup+', [status(thm)], ['33', '34'])).
% 1.30/1.46  thf('36', plain,
% 1.30/1.46      (![X9 : $i, X11 : $i]:
% 1.30/1.46         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 1.30/1.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.30/1.46  thf('37', plain,
% 1.30/1.46      (((k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)) = (k1_xboole_0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['35', '36'])).
% 1.30/1.46  thf('38', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.46         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.30/1.46          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['9', '10'])).
% 1.30/1.46  thf('39', plain,
% 1.30/1.46      ((((k1_xboole_0) != (k1_xboole_0))
% 1.30/1.46        | (r1_tarski @ (k4_xboole_0 @ sk_D @ sk_B_1) @ sk_A))),
% 1.30/1.46      inference('sup-', [status(thm)], ['37', '38'])).
% 1.30/1.46  thf('40', plain, ((r1_tarski @ (k4_xboole_0 @ sk_D @ sk_B_1) @ sk_A)),
% 1.30/1.46      inference('simplify', [status(thm)], ['39'])).
% 1.30/1.46  thf('41', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 1.30/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.46  thf('42', plain,
% 1.30/1.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.30/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.30/1.46  thf('43', plain,
% 1.30/1.46      (![X4 : $i, X5 : $i]:
% 1.30/1.46         ((r1_xboole_0 @ X4 @ X5)
% 1.30/1.46          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 1.30/1.46      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.30/1.46  thf('44', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]:
% 1.30/1.46         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.30/1.46          | (r1_xboole_0 @ X0 @ X1))),
% 1.30/1.46      inference('sup+', [status(thm)], ['42', '43'])).
% 1.30/1.46  thf('45', plain,
% 1.30/1.46      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.30/1.46         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 1.30/1.46          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.30/1.46      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.30/1.46  thf('46', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]:
% 1.30/1.46         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['44', '45'])).
% 1.30/1.46  thf('47', plain, ((r1_xboole_0 @ sk_B_1 @ sk_D)),
% 1.30/1.46      inference('sup-', [status(thm)], ['41', '46'])).
% 1.30/1.46  thf('48', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]:
% 1.30/1.46         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['15', '16'])).
% 1.30/1.46  thf('49', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['47', '48'])).
% 1.30/1.46  thf('50', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.30/1.46           = (k4_xboole_0 @ X0 @ X1))),
% 1.30/1.46      inference('sup+', [status(thm)], ['19', '20'])).
% 1.30/1.46  thf('51', plain,
% 1.30/1.46      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 1.30/1.46      inference('sup+', [status(thm)], ['49', '50'])).
% 1.30/1.46  thf('52', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.30/1.46      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.46  thf('53', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 1.30/1.46      inference('demod', [status(thm)], ['51', '52'])).
% 1.30/1.46  thf('54', plain, ((r1_tarski @ sk_D @ sk_A)),
% 1.30/1.46      inference('demod', [status(thm)], ['40', '53'])).
% 1.30/1.46  thf('55', plain,
% 1.30/1.46      (![X9 : $i, X11 : $i]:
% 1.30/1.46         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 1.30/1.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.30/1.46  thf('56', plain, (((k4_xboole_0 @ sk_D @ sk_A) = (k1_xboole_0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['54', '55'])).
% 1.30/1.46  thf('57', plain,
% 1.30/1.46      (![X18 : $i, X19 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.30/1.46           = (k3_xboole_0 @ X18 @ X19))),
% 1.30/1.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.46  thf('58', plain,
% 1.30/1.46      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k3_xboole_0 @ sk_D @ sk_A))),
% 1.30/1.46      inference('sup+', [status(thm)], ['56', '57'])).
% 1.30/1.46  thf('59', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.30/1.46      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.46  thf('60', plain,
% 1.30/1.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.30/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.30/1.46  thf('61', plain, (((sk_D) = (k3_xboole_0 @ sk_A @ sk_D))),
% 1.30/1.46      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.30/1.46  thf('62', plain, (((sk_D) = (sk_A))),
% 1.30/1.46      inference('sup+', [status(thm)], ['32', '61'])).
% 1.30/1.46  thf('63', plain,
% 1.30/1.46      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 1.30/1.46      inference('demod', [status(thm)], ['2', '62'])).
% 1.30/1.46  thf('64', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.30/1.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.30/1.46  thf('65', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['47', '48'])).
% 1.30/1.46  thf('66', plain,
% 1.30/1.46      (![X16 : $i, X17 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17))
% 1.30/1.46           = (k4_xboole_0 @ X16 @ X17))),
% 1.30/1.46      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.30/1.46  thf('67', plain,
% 1.30/1.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.30/1.46           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.30/1.46      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.30/1.46  thf('68', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.30/1.46           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 1.30/1.46      inference('sup+', [status(thm)], ['66', '67'])).
% 1.30/1.46  thf('69', plain,
% 1.30/1.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.30/1.46           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.30/1.46      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.30/1.46  thf('70', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 1.30/1.46           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 1.30/1.46      inference('demod', [status(thm)], ['68', '69'])).
% 1.30/1.46  thf('71', plain,
% 1.30/1.46      (![X0 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_D @ X0))
% 1.30/1.46           = (k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.30/1.46      inference('sup+', [status(thm)], ['65', '70'])).
% 1.30/1.46  thf('72', plain,
% 1.30/1.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.30/1.46           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.30/1.46      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.30/1.46  thf('73', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.30/1.46      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.46  thf('74', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 1.30/1.46           = (k4_xboole_0 @ X1 @ X0))),
% 1.30/1.46      inference('sup+', [status(thm)], ['72', '73'])).
% 1.30/1.46  thf('75', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.30/1.46      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.46  thf('76', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['5', '6'])).
% 1.30/1.46  thf('77', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.46         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.30/1.46          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['9', '10'])).
% 1.30/1.46  thf('78', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]:
% 1.30/1.46         (((k1_xboole_0) != (k1_xboole_0))
% 1.30/1.46          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['76', '77'])).
% 1.30/1.46  thf('79', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 1.30/1.46      inference('simplify', [status(thm)], ['78'])).
% 1.30/1.46  thf('80', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.30/1.46      inference('sup+', [status(thm)], ['75', '79'])).
% 1.30/1.46  thf('81', plain,
% 1.30/1.46      (![X9 : $i, X11 : $i]:
% 1.30/1.46         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 1.30/1.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.30/1.46  thf('82', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['80', '81'])).
% 1.30/1.46  thf('83', plain,
% 1.30/1.46      (![X0 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 1.30/1.46      inference('sup+', [status(thm)], ['74', '82'])).
% 1.30/1.46  thf('84', plain,
% 1.30/1.46      (![X18 : $i, X19 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.30/1.46           = (k3_xboole_0 @ X18 @ X19))),
% 1.30/1.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.46  thf('85', plain,
% 1.30/1.46      (![X0 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 1.30/1.46           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 1.30/1.46      inference('sup+', [status(thm)], ['83', '84'])).
% 1.30/1.46  thf('86', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.30/1.46      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.46  thf('87', plain,
% 1.30/1.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.30/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.30/1.46  thf('88', plain,
% 1.30/1.46      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 1.30/1.46      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.30/1.46  thf('89', plain,
% 1.30/1.46      (![X9 : $i, X11 : $i]:
% 1.30/1.46         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 1.30/1.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.30/1.46  thf('90', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['88', '89'])).
% 1.30/1.46  thf('91', plain,
% 1.30/1.46      (![X18 : $i, X19 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.30/1.46           = (k3_xboole_0 @ X18 @ X19))),
% 1.30/1.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.46  thf('92', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 1.30/1.46           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.30/1.46      inference('sup+', [status(thm)], ['90', '91'])).
% 1.30/1.46  thf('93', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.30/1.46      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.46  thf('94', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]:
% 1.30/1.46         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.30/1.46      inference('demod', [status(thm)], ['92', '93'])).
% 1.30/1.46  thf('95', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.30/1.46      inference('demod', [status(thm)], ['85', '86', '87', '94'])).
% 1.30/1.46  thf('96', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.30/1.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.30/1.46  thf('97', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.30/1.46      inference('sup+', [status(thm)], ['95', '96'])).
% 1.30/1.46  thf('98', plain,
% 1.30/1.46      (![X0 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_D @ X0))
% 1.30/1.46           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 1.30/1.46      inference('demod', [status(thm)], ['71', '97'])).
% 1.30/1.46  thf('99', plain, (((sk_D) = (sk_A))),
% 1.30/1.46      inference('sup+', [status(thm)], ['32', '61'])).
% 1.30/1.46  thf('100', plain,
% 1.30/1.46      (![X0 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_A @ X0))
% 1.30/1.46           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 1.30/1.46      inference('demod', [status(thm)], ['98', '99'])).
% 1.30/1.46  thf('101', plain,
% 1.30/1.46      (![X0 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ X0 @ sk_A))
% 1.30/1.46           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 1.30/1.46      inference('sup+', [status(thm)], ['64', '100'])).
% 1.30/1.46  thf('102', plain,
% 1.30/1.46      (((k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_B_1 @ sk_A))
% 1.30/1.46         = (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.30/1.46      inference('sup+', [status(thm)], ['63', '101'])).
% 1.30/1.46  thf('103', plain,
% 1.30/1.46      (![X0 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ X0 @ sk_A))
% 1.30/1.46           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 1.30/1.46      inference('sup+', [status(thm)], ['64', '100'])).
% 1.30/1.46  thf('104', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['80', '81'])).
% 1.30/1.46  thf('105', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.30/1.46      inference('demod', [status(thm)], ['102', '103', '104'])).
% 1.30/1.46  thf('106', plain,
% 1.30/1.46      (![X18 : $i, X19 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.30/1.46           = (k3_xboole_0 @ X18 @ X19))),
% 1.30/1.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.46  thf('107', plain,
% 1.30/1.46      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.30/1.46      inference('sup+', [status(thm)], ['105', '106'])).
% 1.30/1.46  thf('108', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.30/1.46      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.46  thf('109', plain,
% 1.30/1.46      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 1.30/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.46  thf('110', plain,
% 1.30/1.46      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 1.30/1.46      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.30/1.46  thf('111', plain, ((r1_tarski @ sk_C_1 @ (k2_xboole_0 @ sk_A @ sk_B_1))),
% 1.30/1.46      inference('sup+', [status(thm)], ['109', '110'])).
% 1.30/1.46  thf('112', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.30/1.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.30/1.46  thf('113', plain, ((r1_tarski @ sk_C_1 @ (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 1.30/1.46      inference('demod', [status(thm)], ['111', '112'])).
% 1.30/1.46  thf('114', plain,
% 1.30/1.46      (![X9 : $i, X11 : $i]:
% 1.30/1.46         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 1.30/1.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.30/1.46  thf('115', plain,
% 1.30/1.46      (((k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B_1 @ sk_A)) = (k1_xboole_0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['113', '114'])).
% 1.30/1.46  thf('116', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.30/1.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.30/1.46  thf('117', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.46         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.30/1.46          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['9', '10'])).
% 1.30/1.46  thf('118', plain,
% 1.30/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.46         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.30/1.46          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 1.30/1.46      inference('sup-', [status(thm)], ['116', '117'])).
% 1.30/1.46  thf('119', plain,
% 1.30/1.46      ((((k1_xboole_0) != (k1_xboole_0))
% 1.30/1.46        | (r1_tarski @ (k4_xboole_0 @ sk_C_1 @ sk_A) @ sk_B_1))),
% 1.30/1.46      inference('sup-', [status(thm)], ['115', '118'])).
% 1.30/1.46  thf('120', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['14', '17'])).
% 1.30/1.46  thf('121', plain,
% 1.30/1.46      (![X16 : $i, X17 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17))
% 1.30/1.46           = (k4_xboole_0 @ X16 @ X17))),
% 1.30/1.46      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.30/1.46  thf('122', plain,
% 1.30/1.46      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 1.30/1.46      inference('sup+', [status(thm)], ['120', '121'])).
% 1.30/1.46  thf('123', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.30/1.46      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.46  thf('124', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 1.30/1.46      inference('demod', [status(thm)], ['122', '123'])).
% 1.30/1.46  thf('125', plain,
% 1.30/1.46      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_C_1 @ sk_B_1))),
% 1.30/1.46      inference('demod', [status(thm)], ['119', '124'])).
% 1.30/1.46  thf('126', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 1.30/1.46      inference('simplify', [status(thm)], ['125'])).
% 1.30/1.46  thf('127', plain,
% 1.30/1.46      (![X9 : $i, X11 : $i]:
% 1.30/1.46         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 1.30/1.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.30/1.46  thf('128', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))),
% 1.30/1.46      inference('sup-', [status(thm)], ['126', '127'])).
% 1.30/1.46  thf('129', plain,
% 1.30/1.46      (![X18 : $i, X19 : $i]:
% 1.30/1.46         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.30/1.46           = (k3_xboole_0 @ X18 @ X19))),
% 1.30/1.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.46  thf('130', plain,
% 1.30/1.46      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 1.30/1.46      inference('sup+', [status(thm)], ['128', '129'])).
% 1.30/1.46  thf('131', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.30/1.46      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.46  thf('132', plain,
% 1.30/1.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.30/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.30/1.46  thf('133', plain, (((sk_C_1) = (k3_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.30/1.46      inference('demod', [status(thm)], ['130', '131', '132'])).
% 1.30/1.46  thf('134', plain, (((sk_B_1) = (sk_C_1))),
% 1.30/1.46      inference('demod', [status(thm)], ['107', '108', '133'])).
% 1.30/1.46  thf('135', plain, (((sk_C_1) != (sk_B_1))),
% 1.30/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.46  thf('136', plain, ($false),
% 1.30/1.46      inference('simplify_reflect-', [status(thm)], ['134', '135'])).
% 1.30/1.46  
% 1.30/1.46  % SZS output end Refutation
% 1.30/1.46  
% 1.30/1.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
