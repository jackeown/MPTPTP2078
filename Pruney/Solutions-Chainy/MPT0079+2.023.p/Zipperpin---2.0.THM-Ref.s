%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bxCLUJQhNo

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:59 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 840 expanded)
%              Number of leaves         :   28 ( 291 expanded)
%              Depth                    :   18
%              Number of atoms          :  872 (6461 expanded)
%              Number of equality atoms :  106 ( 743 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
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
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
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
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('8',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
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

thf('11',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['13','14'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

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
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','33','34'])).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['19','39'])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('58',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_D ) @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('61',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('63',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_C_1 @ sk_D ) )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('66',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_D )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('68',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('70',plain,(
    r1_tarski @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('74',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('76',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('77',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf('81',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('82',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('84',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
    = sk_B_1 ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
    = sk_D ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
    = sk_D ),
    inference('sup+',[status(thm)],['84','85'])).

thf('88',plain,
    ( sk_D
    = ( k3_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['79','86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('91',plain,(
    sk_D = sk_A ),
    inference(demod,[status(thm)],['58','88','89','90'])).

thf('92',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','91'])).

thf('93',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('94',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('96',plain,(
    sk_D = sk_A ),
    inference(demod,[status(thm)],['58','88','89','90'])).

thf('97',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('98',plain,(
    sk_D = sk_A ),
    inference(demod,[status(thm)],['58','88','89','90'])).

thf('99',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['15','18'])).

thf('100',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('102',plain,(
    sk_C_1 = sk_B_1 ),
    inference(demod,[status(thm)],['94','100','101'])).

thf('103',plain,(
    sk_C_1 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bxCLUJQhNo
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 636 iterations in 0.224s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.68  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.68  thf(t72_xboole_1, conjecture,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.46/0.68         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.46/0.68       ( ( C ) = ( B ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.46/0.68            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.46/0.68          ( ( C ) = ( B ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.46/0.68  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t4_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.68            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.68       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.68            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.68  thf('1', plain,
% 0.46/0.68      (![X4 : $i, X5 : $i]:
% 0.46/0.68         ((r1_xboole_0 @ X4 @ X5)
% 0.46/0.68          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.68  thf('2', plain,
% 0.46/0.68      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.46/0.68          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.46/0.68      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.68  thf('4', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.68          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['1', '4'])).
% 0.46/0.68  thf('6', plain, ((r1_xboole_0 @ sk_B_1 @ sk_D)),
% 0.46/0.68      inference('sup-', [status(thm)], ['0', '5'])).
% 0.46/0.68  thf(t7_xboole_0, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.68          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.46/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.46/0.68          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.46/0.68      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.68  thf('10', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['6', '9'])).
% 0.46/0.68  thf('11', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.68  thf('13', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.68  thf(t51_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.46/0.68       ( A ) ))).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (![X27 : $i, X28 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 0.46/0.68           = (X27))),
% 0.46/0.68      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_A)) = (sk_C_1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.68  thf(commutativity_k2_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.68  thf(t1_boole, axiom,
% 0.46/0.68    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.68  thf('17', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.46/0.68      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.68  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.68  thf('19', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['15', '18'])).
% 0.46/0.68  thf('20', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.46/0.68      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.68  thf(t6_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      (![X29 : $i, X30 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X29 @ (k2_xboole_0 @ X29 @ X30))
% 0.46/0.68           = (k2_xboole_0 @ X29 @ X30))),
% 0.46/0.68      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.46/0.68  thf('22', plain,
% 0.46/0.68      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['20', '21'])).
% 0.46/0.68  thf('23', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.46/0.68      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.68  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.68  thf(t41_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.68       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.68  thf('25', plain,
% 0.46/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.46/0.68           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.68  thf('26', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.68           = (k4_xboole_0 @ X1 @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['24', '25'])).
% 0.46/0.68  thf(t48_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      (![X22 : $i, X23 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.46/0.68           = (k3_xboole_0 @ X22 @ X23))),
% 0.46/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.46/0.68           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.68  thf('29', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.46/0.68      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.68  thf(t7_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 0.46/0.68      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.68  thf('31', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.68      inference('sup+', [status(thm)], ['29', '30'])).
% 0.46/0.68  thf(l32_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.68  thf('32', plain,
% 0.46/0.68      (![X9 : $i, X11 : $i]:
% 0.46/0.68         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.68  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.68  thf('34', plain,
% 0.46/0.68      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.68  thf('35', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['28', '33', '34'])).
% 0.46/0.68  thf('36', plain,
% 0.46/0.68      (![X27 : $i, X28 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 0.46/0.68           = (X27))),
% 0.46/0.68      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.46/0.68  thf('37', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.68           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['35', '36'])).
% 0.46/0.68  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.68  thf('39', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.68  thf('40', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['19', '39'])).
% 0.46/0.68  thf('41', plain,
% 0.46/0.68      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('42', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.68  thf('43', plain,
% 0.46/0.68      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.68      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.68  thf('44', plain,
% 0.46/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.46/0.68           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.68  thf('45', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D)
% 0.46/0.68           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['43', '44'])).
% 0.46/0.68  thf('46', plain,
% 0.46/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.46/0.68           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.68  thf('47', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D)
% 0.46/0.68           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B_1) @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.68  thf('48', plain,
% 0.46/0.68      (((k4_xboole_0 @ sk_A @ sk_D)
% 0.46/0.68         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['40', '47'])).
% 0.46/0.68  thf('49', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.68  thf('50', plain,
% 0.46/0.68      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 0.46/0.68      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.68  thf('51', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['49', '50'])).
% 0.46/0.68  thf('52', plain,
% 0.46/0.68      (![X9 : $i, X11 : $i]:
% 0.46/0.68         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.68  thf('53', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.68  thf('54', plain,
% 0.46/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.46/0.68           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.68  thf('55', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.68  thf('56', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['48', '55'])).
% 0.46/0.68  thf('57', plain,
% 0.46/0.68      (![X27 : $i, X28 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 0.46/0.68           = (X27))),
% 0.46/0.68      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.46/0.68  thf('58', plain,
% 0.46/0.68      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_D) @ k1_xboole_0) = (sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['56', '57'])).
% 0.46/0.68  thf('59', plain,
% 0.46/0.68      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.68      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.68  thf(t40_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf('60', plain,
% 0.46/0.68      (![X17 : $i, X18 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 0.46/0.68           = (k4_xboole_0 @ X17 @ X18))),
% 0.46/0.68      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.68  thf('61', plain,
% 0.46/0.68      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D)
% 0.46/0.68         = (k4_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.68      inference('sup+', [status(thm)], ['59', '60'])).
% 0.46/0.68  thf(t39_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf('62', plain,
% 0.46/0.68      (![X14 : $i, X15 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.46/0.68           = (k2_xboole_0 @ X14 @ X15))),
% 0.46/0.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.68  thf('63', plain,
% 0.46/0.68      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_C_1 @ sk_D))
% 0.46/0.68         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['61', '62'])).
% 0.46/0.68  thf('64', plain,
% 0.46/0.68      (![X14 : $i, X15 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.46/0.68           = (k2_xboole_0 @ X14 @ X15))),
% 0.46/0.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.68  thf('65', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.68  thf('66', plain,
% 0.46/0.68      (((k2_xboole_0 @ sk_C_1 @ sk_D)
% 0.46/0.68         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.46/0.68  thf('67', plain,
% 0.46/0.68      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.68      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.68  thf('68', plain,
% 0.46/0.68      (((k2_xboole_0 @ sk_B_1 @ sk_A)
% 0.46/0.68         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.68  thf('69', plain,
% 0.46/0.68      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 0.46/0.68      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.68  thf('70', plain, ((r1_tarski @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['68', '69'])).
% 0.46/0.68  thf('71', plain,
% 0.46/0.68      (![X9 : $i, X11 : $i]:
% 0.46/0.68         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.68  thf('72', plain,
% 0.46/0.68      (((k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)) = (k1_xboole_0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['70', '71'])).
% 0.46/0.68  thf('73', plain,
% 0.46/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.46/0.68           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.68  thf('74', plain,
% 0.46/0.68      (((k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B_1) @ sk_A) = (k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.68  thf('75', plain,
% 0.46/0.68      (![X22 : $i, X23 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.46/0.68           = (k3_xboole_0 @ X22 @ X23))),
% 0.46/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.68  thf('76', plain,
% 0.46/0.68      (((k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B_1) @ k1_xboole_0)
% 0.46/0.68         = (k3_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B_1) @ sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['74', '75'])).
% 0.46/0.68  thf(t3_boole, axiom,
% 0.46/0.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.68  thf('77', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.68  thf('78', plain,
% 0.46/0.68      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.68  thf('79', plain,
% 0.46/0.68      (((k4_xboole_0 @ sk_D @ sk_B_1)
% 0.46/0.68         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B_1)))),
% 0.46/0.68      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.46/0.68  thf('80', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['6', '9'])).
% 0.46/0.68  thf('81', plain,
% 0.46/0.68      (![X27 : $i, X28 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 0.46/0.68           = (X27))),
% 0.46/0.68      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.46/0.68  thf('82', plain,
% 0.46/0.68      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_D)) = (sk_B_1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['80', '81'])).
% 0.46/0.68  thf('83', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.68  thf('84', plain, (((k4_xboole_0 @ sk_B_1 @ sk_D) = (sk_B_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['82', '83'])).
% 0.46/0.68  thf('85', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.68  thf('86', plain, (((k4_xboole_0 @ sk_D @ sk_B_1) = (sk_D))),
% 0.46/0.68      inference('sup+', [status(thm)], ['84', '85'])).
% 0.46/0.68  thf('87', plain, (((k4_xboole_0 @ sk_D @ sk_B_1) = (sk_D))),
% 0.46/0.68      inference('sup+', [status(thm)], ['84', '85'])).
% 0.46/0.68  thf('88', plain, (((sk_D) = (k3_xboole_0 @ sk_A @ sk_D))),
% 0.46/0.68      inference('demod', [status(thm)], ['79', '86', '87'])).
% 0.46/0.68  thf('89', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.68  thf('90', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.68  thf('91', plain, (((sk_D) = (sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['58', '88', '89', '90'])).
% 0.46/0.68  thf('92', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '91'])).
% 0.46/0.68  thf('93', plain,
% 0.46/0.68      (![X27 : $i, X28 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 0.46/0.68           = (X27))),
% 0.46/0.68      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.46/0.68  thf('94', plain,
% 0.46/0.68      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_A)) = (sk_B_1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['92', '93'])).
% 0.46/0.68  thf('95', plain,
% 0.46/0.68      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D)
% 0.46/0.68         = (k4_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.68      inference('sup+', [status(thm)], ['59', '60'])).
% 0.46/0.68  thf('96', plain, (((sk_D) = (sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['58', '88', '89', '90'])).
% 0.46/0.68  thf('97', plain,
% 0.46/0.68      (![X17 : $i, X18 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 0.46/0.68           = (k4_xboole_0 @ X17 @ X18))),
% 0.46/0.68      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.68  thf('98', plain, (((sk_D) = (sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['58', '88', '89', '90'])).
% 0.46/0.68  thf('99', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['15', '18'])).
% 0.46/0.68  thf('100', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 0.46/0.68  thf('101', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.68  thf('102', plain, (((sk_C_1) = (sk_B_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['94', '100', '101'])).
% 0.46/0.68  thf('103', plain, (((sk_C_1) != (sk_B_1))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('104', plain, ($false),
% 0.46/0.68      inference('simplify_reflect-', [status(thm)], ['102', '103'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
