%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mqZfMlGxTO

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:02 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 916 expanded)
%              Number of leaves         :   27 ( 315 expanded)
%              Depth                    :   28
%              Number of atoms          : 1186 (7412 expanded)
%              Number of equality atoms :  140 ( 857 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','11','14'])).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k2_xboole_0 @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k2_xboole_0 @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_C_1 ) @ sk_A )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_C_1 )
    = ( k4_xboole_0 @ sk_D @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('50',plain,(
    r1_tarski @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('54',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('56',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('57',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('62',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('63',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','63'])).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('66',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('69',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k2_xboole_0 @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ X0 )
      = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ X0 ) )
      = ( k2_xboole_0 @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['47','71'])).

thf('73',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ X0 ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ X0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('77',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('78',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','81'])).

thf('83',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['31','36','82'])).

thf('84',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('85',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('88',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('90',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('92',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('94',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_C_1 )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('96',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_C_1 )
    = ( k4_xboole_0 @ sk_D @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('97',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('99',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('100',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('102',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('104',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('106',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['97','106'])).

thf('108',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('109',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A )
    = ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_D @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['107','110'])).

thf('112',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('113',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('114',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['97','106'])).

thf('115',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('117',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('119',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('121',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['111','112','113','114','121'])).

thf('123',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('125',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_D ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('127',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('129',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('131',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['97','106'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('134',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('136',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('138',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['131','138'])).

thf('140',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['122','139'])).

thf('141',plain,(
    sk_C_1 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['140','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mqZfMlGxTO
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 478 iterations in 0.194s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(t72_xboole_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.46/0.65         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.46/0.65       ( ( C ) = ( B ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.46/0.65            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.46/0.65          ( ( C ) = ( B ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(commutativity_k2_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.65  thf(t7_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.65  thf('4', plain, ((r1_tarski @ sk_C_1 @ (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['2', '3'])).
% 0.46/0.65  thf(l32_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X10 : $i, X12 : $i]:
% 0.46/0.65         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.46/0.65          | ~ (r1_tarski @ X10 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B_1 @ sk_A)) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.65  thf(t41_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.65       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.46/0.65           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_B_1) @ sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf(t39_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.46/0.65           = (k2_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 0.46/0.65         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C_1 @ sk_B_1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf(t1_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.65  thf('13', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.65  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C_1 @ sk_B_1)))),
% 0.46/0.65      inference('demod', [status(thm)], ['10', '11', '14'])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.46/0.65           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.46/0.65           = (k2_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.46/0.65           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.46/0.65           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.46/0.65      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.65  thf(t4_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.65       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ (k2_xboole_0 @ X26 @ X27) @ X28)
% 0.46/0.65           = (k2_xboole_0 @ X26 @ (k2_xboole_0 @ X27 @ X28)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.46/0.65           = (k2_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ (k2_xboole_0 @ X26 @ X27) @ X28)
% 0.46/0.65           = (k2_xboole_0 @ X26 @ (k2_xboole_0 @ X27 @ X28)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))
% 0.46/0.65           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B_1 @ sk_A)
% 0.46/0.65         = (k2_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_A @ sk_C_1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['15', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B_1 @ sk_A)
% 0.46/0.65         = (k2_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf(t40_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 0.46/0.65           = (k4_xboole_0 @ X17 @ X18))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.46/0.65           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ 
% 0.46/0.65           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1) @ 
% 0.46/0.65           X0) = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.46/0.65           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ 
% 0.46/0.65           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1) @ 
% 0.46/0.65           X0) = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (((k4_xboole_0 @ 
% 0.46/0.65         (k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_C_1) @ sk_A)
% 0.46/0.65         = (k4_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['25', '30'])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 0.46/0.65           = (k4_xboole_0 @ X17 @ X18))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.65           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_C_1)
% 0.46/0.65         = (k4_xboole_0 @ sk_D @ sk_C_1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['32', '35'])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X10 : $i, X12 : $i]:
% 0.46/0.65         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.46/0.65          | ~ (r1_tarski @ X10 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.46/0.65           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.46/0.65           = (k2_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.46/0.65           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['43', '44'])).
% 0.46/0.65  thf('46', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf('50', plain, ((r1_tarski @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['48', '49'])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (![X10 : $i, X12 : $i]:
% 0.46/0.65         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.46/0.65          | ~ (r1_tarski @ X10 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.46/0.65           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B_1) @ sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['52', '53'])).
% 0.46/0.65  thf('55', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t7_xboole_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.65          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.65  thf(t4_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.46/0.65          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.65  thf('59', plain, (((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['55', '58'])).
% 0.46/0.65  thf(t47_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 0.46/0.65           = (k4_xboole_0 @ X22 @ X23))),
% 0.46/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['59', '60'])).
% 0.46/0.65  thf(t3_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.65  thf('62', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf('63', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['61', '62'])).
% 0.46/0.65  thf('64', plain, (((k4_xboole_0 @ sk_D @ sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['54', '63'])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.46/0.65           = (k2_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.46/0.65      inference('sup+', [status(thm)], ['64', '65'])).
% 0.46/0.65  thf('67', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('68', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf('69', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.46/0.65  thf('70', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ (k2_xboole_0 @ X26 @ X27) @ X28)
% 0.46/0.65           = (k2_xboole_0 @ X26 @ (k2_xboole_0 @ X27 @ X28)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.46/0.65  thf('71', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ sk_A @ X0)
% 0.46/0.65           = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_D @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['69', '70'])).
% 0.46/0.65  thf('72', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ X0))
% 0.46/0.65           = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.46/0.65      inference('sup+', [status(thm)], ['47', '71'])).
% 0.46/0.65  thf('73', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.46/0.65  thf('74', plain,
% 0.46/0.65      (![X0 : $i]: ((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ X0)) = (sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.65  thf('75', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.65           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('76', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ sk_A @ sk_A)
% 0.46/0.65           = (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ X0) @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['74', '75'])).
% 0.46/0.65  thf(idempotence_k2_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.65  thf('77', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.46/0.65      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.46/0.65  thf('78', plain,
% 0.46/0.65      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.65  thf('79', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.65      inference('sup+', [status(thm)], ['77', '78'])).
% 0.46/0.65  thf('80', plain,
% 0.46/0.65      (![X10 : $i, X12 : $i]:
% 0.46/0.65         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.46/0.65          | ~ (r1_tarski @ X10 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.65  thf('81', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['79', '80'])).
% 0.46/0.65  thf('82', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ X0) @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['76', '81'])).
% 0.46/0.65  thf('83', plain,
% 0.46/0.65      (((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['31', '36', '82'])).
% 0.46/0.65  thf('84', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.46/0.65           = (k2_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.65  thf('85', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 0.46/0.65         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['83', '84'])).
% 0.46/0.65  thf('86', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('87', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf('88', plain,
% 0.46/0.65      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.46/0.65  thf('89', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))
% 0.46/0.65           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.46/0.65  thf('90', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_C_1 @ sk_A)
% 0.46/0.65         = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['88', '89'])).
% 0.46/0.65  thf('91', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('92', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_C_1 @ sk_A)
% 0.46/0.65         = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['90', '91'])).
% 0.46/0.65  thf('93', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.65           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('94', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_C_1)
% 0.46/0.65         = (k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_C_1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['92', '93'])).
% 0.46/0.65  thf('95', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.65           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('96', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_C_1)
% 0.46/0.65         = (k4_xboole_0 @ sk_D @ sk_C_1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['32', '35'])).
% 0.46/0.65  thf('97', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_D @ sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.46/0.65  thf('98', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(symmetry_r1_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.46/0.65  thf('99', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i]:
% 0.46/0.65         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.46/0.65  thf('100', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.46/0.65      inference('sup-', [status(thm)], ['98', '99'])).
% 0.46/0.65  thf('101', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.65  thf('102', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['100', '101'])).
% 0.46/0.65  thf('103', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 0.46/0.65           = (k4_xboole_0 @ X22 @ X23))),
% 0.46/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.65  thf('104', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['102', '103'])).
% 0.46/0.65  thf('105', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf('106', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['104', '105'])).
% 0.46/0.65  thf('107', plain, (((sk_A) = (k4_xboole_0 @ sk_D @ sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['97', '106'])).
% 0.46/0.65  thf('108', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.46/0.65           = (k2_xboole_0 @ X14 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.65  thf('109', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 0.46/0.65           = (k4_xboole_0 @ X17 @ X18))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.65  thf('110', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.46/0.65           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['108', '109'])).
% 0.46/0.65  thf('111', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A)
% 0.46/0.65         = (k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_D @ sk_C_1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['107', '110'])).
% 0.46/0.65  thf('112', plain,
% 0.46/0.65      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.65  thf('113', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 0.46/0.65           = (k4_xboole_0 @ X17 @ X18))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.65  thf('114', plain, (((sk_A) = (k4_xboole_0 @ sk_D @ sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['97', '106'])).
% 0.46/0.65  thf('115', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('116', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.65  thf('117', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['115', '116'])).
% 0.46/0.65  thf('118', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 0.46/0.65           = (k4_xboole_0 @ X22 @ X23))),
% 0.46/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.65  thf('119', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['117', '118'])).
% 0.46/0.65  thf('120', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf('121', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['119', '120'])).
% 0.46/0.65  thf('122', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['111', '112', '113', '114', '121'])).
% 0.46/0.65  thf('123', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('124', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i]:
% 0.46/0.65         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.46/0.65  thf('125', plain, ((r1_xboole_0 @ sk_B_1 @ sk_D)),
% 0.46/0.65      inference('sup-', [status(thm)], ['123', '124'])).
% 0.46/0.65  thf('126', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.65  thf('127', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['125', '126'])).
% 0.46/0.65  thf('128', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 0.46/0.65           = (k4_xboole_0 @ X22 @ X23))),
% 0.46/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.65  thf('129', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 0.46/0.65      inference('sup+', [status(thm)], ['127', '128'])).
% 0.46/0.65  thf('130', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf('131', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['129', '130'])).
% 0.46/0.65  thf('132', plain, (((sk_A) = (k4_xboole_0 @ sk_D @ sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['97', '106'])).
% 0.46/0.65  thf('133', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.65  thf('134', plain, (((sk_D) = (k2_xboole_0 @ sk_D @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['132', '133'])).
% 0.46/0.65  thf('135', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.65  thf('136', plain, (((sk_D) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['134', '135'])).
% 0.46/0.65  thf('137', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.46/0.65  thf('138', plain, (((sk_A) = (sk_D))),
% 0.46/0.65      inference('sup+', [status(thm)], ['136', '137'])).
% 0.46/0.65  thf('139', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['131', '138'])).
% 0.46/0.65  thf('140', plain, (((sk_B_1) = (sk_C_1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['122', '139'])).
% 0.46/0.65  thf('141', plain, (((sk_C_1) != (sk_B_1))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('142', plain, ($false),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['140', '141'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
