%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kaJbG0peQe

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:59 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  162 (1898 expanded)
%              Number of leaves         :   27 ( 652 expanded)
%              Depth                    :   22
%              Number of atoms          : 1147 (15766 expanded)
%              Number of equality atoms :  142 (1852 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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

thf('0',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('8',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_C_1 @ sk_D ) )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_D )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k2_xboole_0 @ X24 @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('30',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k2_xboole_0 @ X24 @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ sk_D ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_D ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_D ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('48',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('56',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('57',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('62',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('64',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','65','66'])).

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['55','71'])).

thf('73',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('74',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('76',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('78',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('80',plain,
    ( ( k2_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('83',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('86',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['80','81','84','85'])).

thf('87',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['40','86'])).

thf('88',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('92',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('95',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('97',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('99',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('103',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['87','92'])).

thf('104',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('106',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('109',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    sk_D = sk_A ),
    inference(demod,[status(thm)],['101','102','103','104','109'])).

thf('111',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','110'])).

thf('112',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('113',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['111','116'])).

thf('118',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('119',plain,(
    sk_D = sk_A ),
    inference(demod,[status(thm)],['101','102','103','104','109'])).

thf('120',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('121',plain,(
    sk_D = sk_A ),
    inference(demod,[status(thm)],['101','102','103','104','109'])).

thf('122',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('123',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('124',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('126',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['118','119','120','121','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('129',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','110'])).

thf('130',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('131',plain,(
    sk_C_1 = sk_B_1 ),
    inference(demod,[status(thm)],['117','127','128','129','130'])).

thf('132',plain,(
    sk_C_1 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['131','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kaJbG0peQe
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:24:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 352 iterations in 0.185s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(t72_xboole_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.46/0.64         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.46/0.64       ( ( C ) = ( B ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.46/0.64            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.46/0.64          ( ( C ) = ( B ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.46/0.64  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t4_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.64            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i]:
% 0.46/0.64         ((r1_xboole_0 @ X5 @ X6)
% 0.46/0.64          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.64  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.46/0.64          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.64          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '4'])).
% 0.46/0.64  thf('6', plain, ((r1_xboole_0 @ sk_B_1 @ sk_D)),
% 0.46/0.64      inference('sup-', [status(thm)], ['0', '5'])).
% 0.46/0.64  thf(t7_xboole_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.46/0.64          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf('10', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['6', '9'])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(commutativity_k2_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.64  thf(t40_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.46/0.64           = (k4_xboole_0 @ X15 @ X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D)
% 0.46/0.64         = (k4_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.64      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.64  thf(t39_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.46/0.64           = (k2_xboole_0 @ X12 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_C_1 @ sk_D))
% 0.46/0.64         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.46/0.64           = (k2_xboole_0 @ X12 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_C_1 @ sk_D)
% 0.46/0.64         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_B_1 @ sk_A)
% 0.46/0.64         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.46/0.64           = (k4_xboole_0 @ X15 @ X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.46/0.64           = (k2_xboole_0 @ X12 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.46/0.64           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.46/0.64           = (k2_xboole_0 @ X12 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.64           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (((k2_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D)
% 0.46/0.64         = (k2_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ 
% 0.46/0.64            (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['22', '27'])).
% 0.46/0.64  thf(t4_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.64       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ (k2_xboole_0 @ X24 @ X25) @ X26)
% 0.46/0.64           = (k2_xboole_0 @ X24 @ (k2_xboole_0 @ X25 @ X26)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ (k2_xboole_0 @ X24 @ X25) @ X26)
% 0.46/0.64           = (k2_xboole_0 @ X24 @ (k2_xboole_0 @ X25 @ X26)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.64           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_A @ sk_D))
% 0.46/0.64         = (k2_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.46/0.64           = (k4_xboole_0 @ X15 @ X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.64           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (((k4_xboole_0 @ 
% 0.46/0.64         (k2_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_B_1 @ sk_A)) @ sk_B_1)
% 0.46/0.64         = (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_D) @ sk_B_1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['33', '36'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.64           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.64           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_A @ sk_B_1)
% 0.46/0.64         = (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_D) @ sk_B_1))),
% 0.46/0.64      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.46/0.64  thf('41', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf('43', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf(t47_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 0.46/0.64           = (k4_xboole_0 @ X20 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.64           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['44', '45'])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['43', '46'])).
% 0.46/0.64  thf(t3_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.64  thf('48', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.64  thf('49', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.46/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.64  thf(t41_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.64       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.46/0.64           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D)
% 0.46/0.64           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.46/0.64           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D)
% 0.46/0.64           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B_1) @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['52', '53'])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_A @ sk_D)
% 0.46/0.64         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['49', '54'])).
% 0.46/0.64  thf(idempotence_k2_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.64  thf('56', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.46/0.64           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.64           = (k4_xboole_0 @ X1 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['56', '57'])).
% 0.46/0.64  thf(t48_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.46/0.64           = (k3_xboole_0 @ X22 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.46/0.64           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['58', '59'])).
% 0.46/0.64  thf('61', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.46/0.64           = (k3_xboole_0 @ X22 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['61', '62'])).
% 0.46/0.64  thf(t2_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.64  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['63', '64'])).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['60', '65', '66'])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 0.46/0.64           = (k4_xboole_0 @ X20 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.46/0.64           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['67', '68'])).
% 0.46/0.64  thf('70', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      (((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_D)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['55', '71'])).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.46/0.64           = (k3_xboole_0 @ X22 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf('74', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 0.46/0.64           = (k4_xboole_0 @ X20 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_D))),
% 0.46/0.64      inference('sup+', [status(thm)], ['74', '75'])).
% 0.46/0.64  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['63', '64'])).
% 0.46/0.64  thf('78', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['76', '77'])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.46/0.64           = (k2_xboole_0 @ X12 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_D @ k1_xboole_0) = (k2_xboole_0 @ sk_D @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['78', '79'])).
% 0.46/0.64  thf('81', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.64  thf(t1_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.64  thf('83', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.64  thf('84', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['82', '83'])).
% 0.46/0.64  thf('85', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.64  thf('86', plain, (((sk_D) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['80', '81', '84', '85'])).
% 0.46/0.64  thf('87', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.46/0.64      inference('demod', [status(thm)], ['40', '86'])).
% 0.46/0.64  thf('88', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['6', '9'])).
% 0.46/0.64  thf('89', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.64           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['44', '45'])).
% 0.46/0.64  thf('90', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['88', '89'])).
% 0.46/0.64  thf('91', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.64  thf('92', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.46/0.64      inference('demod', [status(thm)], ['90', '91'])).
% 0.46/0.64  thf('93', plain, (((sk_D) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['87', '92'])).
% 0.46/0.64  thf('94', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.46/0.64           = (k3_xboole_0 @ X22 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf('95', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_A @ sk_D) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['93', '94'])).
% 0.46/0.64  thf('96', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf('97', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_A @ sk_D) = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['95', '96'])).
% 0.46/0.64  thf('98', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 0.46/0.64           = (k4_xboole_0 @ X20 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.64  thf('99', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.46/0.64           = (k3_xboole_0 @ X22 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf('100', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.46/0.64           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['98', '99'])).
% 0.46/0.64  thf('101', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A))
% 0.46/0.64         = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_D)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['97', '100'])).
% 0.46/0.64  thf('102', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.64           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['44', '45'])).
% 0.46/0.64  thf('103', plain, (((sk_D) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['87', '92'])).
% 0.46/0.64  thf('104', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.64  thf('105', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['63', '64'])).
% 0.46/0.64  thf('106', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.46/0.64           = (k3_xboole_0 @ X22 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf('107', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['105', '106'])).
% 0.46/0.64  thf('108', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.64  thf('109', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['107', '108'])).
% 0.46/0.64  thf('110', plain, (((sk_D) = (sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['101', '102', '103', '104', '109'])).
% 0.46/0.64  thf('111', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['10', '110'])).
% 0.46/0.64  thf('112', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 0.46/0.64           = (k4_xboole_0 @ X20 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.64  thf('113', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.46/0.64           = (k2_xboole_0 @ X12 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.64  thf('114', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.46/0.64           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['112', '113'])).
% 0.46/0.64  thf('115', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.64  thf('116', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.46/0.64           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['114', '115'])).
% 0.46/0.64  thf('117', plain,
% 0.46/0.64      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_A))
% 0.46/0.64         = (k2_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['111', '116'])).
% 0.46/0.64  thf('118', plain,
% 0.46/0.64      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D)
% 0.46/0.64         = (k4_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.64      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.64  thf('119', plain, (((sk_D) = (sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['101', '102', '103', '104', '109'])).
% 0.46/0.64  thf('120', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.46/0.64           = (k4_xboole_0 @ X15 @ X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.64  thf('121', plain, (((sk_D) = (sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['101', '102', '103', '104', '109'])).
% 0.46/0.64  thf('122', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.64  thf('123', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 0.46/0.64           = (k4_xboole_0 @ X20 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.64  thf('124', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['122', '123'])).
% 0.46/0.64  thf('125', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.64  thf('126', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['124', '125'])).
% 0.46/0.64  thf('127', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.46/0.64      inference('demod', [status(thm)], ['118', '119', '120', '121', '126'])).
% 0.46/0.64  thf('128', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['82', '83'])).
% 0.46/0.64  thf('129', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['10', '110'])).
% 0.46/0.64  thf('130', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.64  thf('131', plain, (((sk_C_1) = (sk_B_1))),
% 0.46/0.64      inference('demod', [status(thm)], ['117', '127', '128', '129', '130'])).
% 0.46/0.64  thf('132', plain, (((sk_C_1) != (sk_B_1))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('133', plain, ($false),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['131', '132'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
