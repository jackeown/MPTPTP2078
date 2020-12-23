%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WiC3f4YP6T

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:57 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  205 (2582 expanded)
%              Number of leaves         :   24 ( 879 expanded)
%              Depth                    :   32
%              Number of atoms          : 1476 (20550 expanded)
%              Number of equality atoms :  185 (2401 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_C_1 @ sk_D ) )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_D )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('26',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('30',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('55',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_B_1 )
    = ( k3_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('66',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('72',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('80',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['74','77','78','79'])).

thf('81',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','53','62','63','80'])).

thf('82',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('83',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('87',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('89',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('91',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['85','86','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('94',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('98',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['74','77','78','79'])).

thf('99',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('101',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('103',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('104',plain,
    ( sk_D
    = ( k3_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('106',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_A @ sk_D ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['104','110'])).

thf('112',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('114',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_D ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['85','86','91'])).

thf('116',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_D ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('118',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('119',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('121',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ X0 )
      = ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_D ) )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['116','123'])).

thf('125',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('126',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_D ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('128',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_C_1 )
    = ( k3_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('130',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('131',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('135',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X28 @ X29 ) @ ( k4_xboole_0 @ X28 @ X29 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['129','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_D ) ) ),
    inference(demod,[status(thm)],['128','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('142',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_D ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_D ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('145',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('147',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('148',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('154',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['142','143','144','145','146','147','159'])).

thf('161',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X28 @ X29 ) @ ( k4_xboole_0 @ X28 @ X29 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('162',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_D ) @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,
    ( sk_D
    = ( k3_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('165',plain,(
    sk_D = sk_A ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','165'])).

thf('167',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('168',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['85','86','91'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ X0 )
      = ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('170',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_D )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('172',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_D )
    = sk_C_1 ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = sk_C_1 ),
    inference(demod,[status(thm)],['167','172'])).

thf('174',plain,(
    sk_D = sk_A ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('175',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('176',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['166','176'])).

thf('178',plain,(
    sk_C_1 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['177','178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WiC3f4YP6T
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:40:55 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.05/1.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.22  % Solved by: fo/fo7.sh
% 1.05/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.22  % done 1561 iterations in 0.783s
% 1.05/1.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.22  % SZS output start Refutation
% 1.05/1.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.22  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.05/1.22  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.05/1.22  thf(sk_B_type, type, sk_B: $i > $i).
% 1.05/1.22  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.05/1.22  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.05/1.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.22  thf(sk_D_type, type, sk_D: $i).
% 1.05/1.22  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.05/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.22  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.22  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.05/1.22  thf(t72_xboole_1, conjecture,
% 1.05/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.22     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.05/1.22         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.05/1.22       ( ( C ) = ( B ) ) ))).
% 1.05/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.22    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.22        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.05/1.22            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.05/1.22          ( ( C ) = ( B ) ) ) )),
% 1.05/1.22    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 1.05/1.22  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf(t4_xboole_0, axiom,
% 1.05/1.22    (![A:$i,B:$i]:
% 1.05/1.22     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.05/1.22            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.05/1.22       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.05/1.22            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.05/1.22  thf('1', plain,
% 1.05/1.22      (![X5 : $i, X6 : $i]:
% 1.05/1.22         ((r1_xboole_0 @ X5 @ X6)
% 1.05/1.22          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 1.05/1.22      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.05/1.22  thf(commutativity_k3_xboole_0, axiom,
% 1.05/1.22    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.05/1.22  thf('2', plain,
% 1.05/1.22      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.22  thf('3', plain,
% 1.05/1.22      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.05/1.22         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 1.05/1.22          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.05/1.22      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.05/1.22  thf('4', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.22         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.05/1.22          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.05/1.22      inference('sup-', [status(thm)], ['2', '3'])).
% 1.05/1.22  thf('5', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]:
% 1.05/1.22         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.05/1.22      inference('sup-', [status(thm)], ['1', '4'])).
% 1.05/1.22  thf('6', plain, ((r1_xboole_0 @ sk_B_1 @ sk_D)),
% 1.05/1.22      inference('sup-', [status(thm)], ['0', '5'])).
% 1.05/1.22  thf(t7_xboole_0, axiom,
% 1.05/1.22    (![A:$i]:
% 1.05/1.22     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.05/1.22          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.05/1.22  thf('7', plain,
% 1.05/1.22      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 1.05/1.22      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.05/1.22  thf('8', plain,
% 1.05/1.22      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.05/1.22         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 1.05/1.22          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.05/1.22      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.05/1.22  thf('9', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]:
% 1.05/1.22         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.05/1.22      inference('sup-', [status(thm)], ['7', '8'])).
% 1.05/1.22  thf('10', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 1.05/1.22      inference('sup-', [status(thm)], ['6', '9'])).
% 1.05/1.22  thf(t47_xboole_1, axiom,
% 1.05/1.22    (![A:$i,B:$i]:
% 1.05/1.22     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.05/1.22  thf('11', plain,
% 1.05/1.22      (![X21 : $i, X22 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22))
% 1.05/1.22           = (k4_xboole_0 @ X21 @ X22))),
% 1.05/1.22      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.05/1.22  thf('12', plain,
% 1.05/1.22      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 1.05/1.22      inference('sup+', [status(thm)], ['10', '11'])).
% 1.05/1.22  thf(t3_boole, axiom,
% 1.05/1.22    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.05/1.22  thf('13', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.05/1.22      inference('cnf', [status(esa)], [t3_boole])).
% 1.05/1.22  thf('14', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 1.05/1.22      inference('demod', [status(thm)], ['12', '13'])).
% 1.05/1.22  thf('15', plain,
% 1.05/1.22      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf(commutativity_k2_xboole_0, axiom,
% 1.05/1.22    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.05/1.22  thf('16', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.22  thf('17', plain,
% 1.05/1.22      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 1.05/1.22      inference('demod', [status(thm)], ['15', '16'])).
% 1.05/1.22  thf(t40_xboole_1, axiom,
% 1.05/1.22    (![A:$i,B:$i]:
% 1.05/1.22     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.05/1.22  thf('18', plain,
% 1.05/1.22      (![X16 : $i, X17 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 1.05/1.22           = (k4_xboole_0 @ X16 @ X17))),
% 1.05/1.22      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.05/1.22  thf('19', plain,
% 1.05/1.22      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D)
% 1.05/1.22         = (k4_xboole_0 @ sk_C_1 @ sk_D))),
% 1.05/1.22      inference('sup+', [status(thm)], ['17', '18'])).
% 1.05/1.22  thf(t39_xboole_1, axiom,
% 1.05/1.22    (![A:$i,B:$i]:
% 1.05/1.22     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.05/1.22  thf('20', plain,
% 1.05/1.22      (![X13 : $i, X14 : $i]:
% 1.05/1.22         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 1.05/1.22           = (k2_xboole_0 @ X13 @ X14))),
% 1.05/1.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.05/1.22  thf('21', plain,
% 1.05/1.22      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_C_1 @ sk_D))
% 1.05/1.22         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 1.05/1.22      inference('sup+', [status(thm)], ['19', '20'])).
% 1.05/1.22  thf('22', plain,
% 1.05/1.22      (![X13 : $i, X14 : $i]:
% 1.05/1.22         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 1.05/1.22           = (k2_xboole_0 @ X13 @ X14))),
% 1.05/1.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.05/1.22  thf('23', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.22  thf('24', plain,
% 1.05/1.22      (((k2_xboole_0 @ sk_C_1 @ sk_D)
% 1.05/1.22         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 1.05/1.22      inference('demod', [status(thm)], ['21', '22', '23'])).
% 1.05/1.22  thf('25', plain,
% 1.05/1.22      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 1.05/1.22      inference('demod', [status(thm)], ['15', '16'])).
% 1.05/1.22  thf('26', plain,
% 1.05/1.22      (((k2_xboole_0 @ sk_B_1 @ sk_A)
% 1.05/1.22         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 1.05/1.22      inference('demod', [status(thm)], ['24', '25'])).
% 1.05/1.22  thf('27', plain,
% 1.05/1.22      (![X16 : $i, X17 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 1.05/1.22           = (k4_xboole_0 @ X16 @ X17))),
% 1.05/1.22      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.05/1.22  thf('28', plain,
% 1.05/1.22      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ 
% 1.05/1.22         (k2_xboole_0 @ sk_B_1 @ sk_A))
% 1.05/1.22         = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 1.05/1.22      inference('sup+', [status(thm)], ['26', '27'])).
% 1.05/1.22  thf('29', plain,
% 1.05/1.22      (![X16 : $i, X17 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 1.05/1.22           = (k4_xboole_0 @ X16 @ X17))),
% 1.05/1.22      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.05/1.22  thf('30', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.05/1.22      inference('cnf', [status(esa)], [t3_boole])).
% 1.05/1.22  thf('31', plain,
% 1.05/1.22      (![X0 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['29', '30'])).
% 1.05/1.22  thf('32', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.05/1.22      inference('cnf', [status(esa)], [t3_boole])).
% 1.05/1.22  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['31', '32'])).
% 1.05/1.22  thf('34', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.22  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['33', '34'])).
% 1.05/1.22  thf('36', plain,
% 1.05/1.22      (![X16 : $i, X17 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 1.05/1.22           = (k4_xboole_0 @ X16 @ X17))),
% 1.05/1.22      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.05/1.22  thf('37', plain,
% 1.05/1.22      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['35', '36'])).
% 1.05/1.22  thf('38', plain,
% 1.05/1.22      (((k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A))
% 1.05/1.22         = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 1.05/1.22      inference('demod', [status(thm)], ['28', '37'])).
% 1.05/1.22  thf('39', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.05/1.22      inference('cnf', [status(esa)], [t3_boole])).
% 1.05/1.22  thf(t48_xboole_1, axiom,
% 1.05/1.22    (![A:$i,B:$i]:
% 1.05/1.22     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.05/1.22  thf('40', plain,
% 1.05/1.22      (![X23 : $i, X24 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 1.05/1.22           = (k3_xboole_0 @ X23 @ X24))),
% 1.05/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.05/1.22  thf('41', plain,
% 1.05/1.22      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['39', '40'])).
% 1.05/1.22  thf('42', plain,
% 1.05/1.22      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['35', '36'])).
% 1.05/1.22  thf('43', plain,
% 1.05/1.22      (![X0 : $i]:
% 1.05/1.22         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['41', '42'])).
% 1.05/1.22  thf('44', plain,
% 1.05/1.22      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.22  thf('45', plain,
% 1.05/1.22      (((k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A))
% 1.05/1.22         = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 1.05/1.22      inference('demod', [status(thm)], ['38', '43', '44'])).
% 1.05/1.22  thf('46', plain,
% 1.05/1.22      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['35', '36'])).
% 1.05/1.22  thf(t41_xboole_1, axiom,
% 1.05/1.22    (![A:$i,B:$i,C:$i]:
% 1.05/1.22     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.05/1.22       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.05/1.22  thf('47', plain,
% 1.05/1.22      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 1.05/1.22           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 1.05/1.22      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.05/1.22  thf('48', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 1.05/1.22           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.05/1.22      inference('sup+', [status(thm)], ['46', '47'])).
% 1.05/1.22  thf('49', plain,
% 1.05/1.22      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 1.05/1.22           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 1.05/1.22      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.05/1.22  thf('50', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 1.05/1.22           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.05/1.22      inference('demod', [status(thm)], ['48', '49'])).
% 1.05/1.22  thf('51', plain,
% 1.05/1.22      (![X0 : $i]:
% 1.05/1.22         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['41', '42'])).
% 1.05/1.22  thf('52', plain,
% 1.05/1.22      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.22  thf('53', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 1.05/1.22           = (k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.05/1.22      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.05/1.22  thf('54', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 1.05/1.22      inference('demod', [status(thm)], ['12', '13'])).
% 1.05/1.22  thf('55', plain,
% 1.05/1.22      (![X23 : $i, X24 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 1.05/1.22           = (k3_xboole_0 @ X23 @ X24))),
% 1.05/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.05/1.22  thf('56', plain,
% 1.05/1.22      (((k4_xboole_0 @ sk_B_1 @ sk_B_1) = (k3_xboole_0 @ sk_B_1 @ sk_D))),
% 1.05/1.22      inference('sup+', [status(thm)], ['54', '55'])).
% 1.05/1.22  thf('57', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 1.05/1.22      inference('sup-', [status(thm)], ['6', '9'])).
% 1.05/1.22  thf('58', plain, (((k4_xboole_0 @ sk_B_1 @ sk_B_1) = (k1_xboole_0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['56', '57'])).
% 1.05/1.22  thf('59', plain,
% 1.05/1.22      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 1.05/1.22           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 1.05/1.22      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.05/1.22  thf('60', plain,
% 1.05/1.22      (![X0 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.05/1.22           = (k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 1.05/1.22      inference('sup+', [status(thm)], ['58', '59'])).
% 1.05/1.22  thf('61', plain,
% 1.05/1.22      (![X0 : $i]:
% 1.05/1.22         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['41', '42'])).
% 1.05/1.22  thf('62', plain,
% 1.05/1.22      (![X0 : $i]:
% 1.05/1.22         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 1.05/1.22           = (k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 1.05/1.22      inference('demod', [status(thm)], ['60', '61'])).
% 1.05/1.22  thf('63', plain,
% 1.05/1.22      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.22  thf('64', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf('65', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]:
% 1.05/1.22         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.05/1.22      inference('sup-', [status(thm)], ['7', '8'])).
% 1.05/1.22  thf('66', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 1.05/1.22      inference('sup-', [status(thm)], ['64', '65'])).
% 1.05/1.22  thf('67', plain,
% 1.05/1.22      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.22  thf('68', plain,
% 1.05/1.22      (![X21 : $i, X22 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22))
% 1.05/1.22           = (k4_xboole_0 @ X21 @ X22))),
% 1.05/1.22      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.05/1.22  thf('69', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.05/1.22           = (k4_xboole_0 @ X0 @ X1))),
% 1.05/1.22      inference('sup+', [status(thm)], ['67', '68'])).
% 1.05/1.22  thf('70', plain,
% 1.05/1.22      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.05/1.22      inference('sup+', [status(thm)], ['66', '69'])).
% 1.05/1.22  thf('71', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.05/1.22      inference('cnf', [status(esa)], [t3_boole])).
% 1.05/1.22  thf('72', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.05/1.22      inference('demod', [status(thm)], ['70', '71'])).
% 1.05/1.22  thf('73', plain,
% 1.05/1.22      (![X23 : $i, X24 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 1.05/1.22           = (k3_xboole_0 @ X23 @ X24))),
% 1.05/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.05/1.22  thf('74', plain,
% 1.05/1.22      (((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 1.05/1.22      inference('sup+', [status(thm)], ['72', '73'])).
% 1.05/1.22  thf('75', plain,
% 1.05/1.22      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['39', '40'])).
% 1.05/1.22  thf('76', plain,
% 1.05/1.22      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.22  thf('77', plain,
% 1.05/1.22      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['75', '76'])).
% 1.05/1.22  thf('78', plain,
% 1.05/1.22      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.22  thf('79', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 1.05/1.22      inference('sup-', [status(thm)], ['64', '65'])).
% 1.05/1.22  thf('80', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 1.05/1.22      inference('demod', [status(thm)], ['74', '77', '78', '79'])).
% 1.05/1.22  thf('81', plain,
% 1.05/1.22      (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 1.05/1.22      inference('demod', [status(thm)], ['45', '53', '62', '63', '80'])).
% 1.05/1.22  thf('82', plain,
% 1.05/1.22      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 1.05/1.22           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 1.05/1.22      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.05/1.22  thf('83', plain,
% 1.05/1.22      (![X13 : $i, X14 : $i]:
% 1.05/1.22         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 1.05/1.22           = (k2_xboole_0 @ X13 @ X14))),
% 1.05/1.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.05/1.22  thf('84', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.22         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.05/1.22           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 1.05/1.22      inference('sup+', [status(thm)], ['82', '83'])).
% 1.05/1.22  thf('85', plain,
% 1.05/1.22      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 1.05/1.22         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B_1)))),
% 1.05/1.22      inference('sup+', [status(thm)], ['81', '84'])).
% 1.05/1.22  thf('86', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['31', '32'])).
% 1.05/1.22  thf('87', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 1.05/1.22      inference('sup-', [status(thm)], ['6', '9'])).
% 1.05/1.22  thf('88', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.05/1.22           = (k4_xboole_0 @ X0 @ X1))),
% 1.05/1.22      inference('sup+', [status(thm)], ['67', '68'])).
% 1.05/1.22  thf('89', plain,
% 1.05/1.22      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 1.05/1.22      inference('sup+', [status(thm)], ['87', '88'])).
% 1.05/1.22  thf('90', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.05/1.22      inference('cnf', [status(esa)], [t3_boole])).
% 1.05/1.22  thf('91', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 1.05/1.22      inference('demod', [status(thm)], ['89', '90'])).
% 1.05/1.22  thf('92', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 1.05/1.22      inference('demod', [status(thm)], ['85', '86', '91'])).
% 1.05/1.22  thf('93', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.22  thf('94', plain,
% 1.05/1.22      (![X16 : $i, X17 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 1.05/1.22           = (k4_xboole_0 @ X16 @ X17))),
% 1.05/1.22      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.05/1.22  thf('95', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.05/1.23           = (k4_xboole_0 @ X0 @ X1))),
% 1.05/1.23      inference('sup+', [status(thm)], ['93', '94'])).
% 1.05/1.23  thf('96', plain,
% 1.05/1.23      (((k4_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_D @ sk_A))),
% 1.05/1.23      inference('sup+', [status(thm)], ['92', '95'])).
% 1.05/1.23  thf('97', plain,
% 1.05/1.23      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['75', '76'])).
% 1.05/1.23  thf('98', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 1.05/1.23      inference('demod', [status(thm)], ['74', '77', '78', '79'])).
% 1.05/1.23  thf('99', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 1.05/1.23      inference('demod', [status(thm)], ['96', '97', '98'])).
% 1.05/1.23  thf('100', plain,
% 1.05/1.23      (![X23 : $i, X24 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 1.05/1.23           = (k3_xboole_0 @ X23 @ X24))),
% 1.05/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.05/1.23  thf('101', plain,
% 1.05/1.23      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k3_xboole_0 @ sk_D @ sk_A))),
% 1.05/1.23      inference('sup+', [status(thm)], ['99', '100'])).
% 1.05/1.23  thf('102', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.05/1.23      inference('cnf', [status(esa)], [t3_boole])).
% 1.05/1.23  thf('103', plain,
% 1.05/1.23      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.23  thf('104', plain, (((sk_D) = (k3_xboole_0 @ sk_A @ sk_D))),
% 1.05/1.23      inference('demod', [status(thm)], ['101', '102', '103'])).
% 1.05/1.23  thf('105', plain,
% 1.05/1.23      (![X23 : $i, X24 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 1.05/1.23           = (k3_xboole_0 @ X23 @ X24))),
% 1.05/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.05/1.23  thf('106', plain,
% 1.05/1.23      (![X13 : $i, X14 : $i]:
% 1.05/1.23         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 1.05/1.23           = (k2_xboole_0 @ X13 @ X14))),
% 1.05/1.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.05/1.23  thf('107', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.05/1.23           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 1.05/1.23      inference('sup+', [status(thm)], ['105', '106'])).
% 1.05/1.23  thf('108', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.23  thf('109', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.23  thf('110', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.05/1.23           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.05/1.23      inference('demod', [status(thm)], ['107', '108', '109'])).
% 1.05/1.23  thf('111', plain,
% 1.05/1.23      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_A @ sk_D))
% 1.05/1.23         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_D)))),
% 1.05/1.23      inference('sup+', [status(thm)], ['104', '110'])).
% 1.05/1.23  thf('112', plain,
% 1.05/1.23      (![X13 : $i, X14 : $i]:
% 1.05/1.23         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 1.05/1.23           = (k2_xboole_0 @ X13 @ X14))),
% 1.05/1.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.05/1.23  thf('113', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.23  thf('114', plain,
% 1.05/1.23      (((k2_xboole_0 @ sk_A @ sk_D)
% 1.05/1.23         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_D)))),
% 1.05/1.23      inference('demod', [status(thm)], ['111', '112', '113'])).
% 1.05/1.23  thf('115', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 1.05/1.23      inference('demod', [status(thm)], ['85', '86', '91'])).
% 1.05/1.23  thf('116', plain,
% 1.05/1.23      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_D)))),
% 1.05/1.23      inference('demod', [status(thm)], ['114', '115'])).
% 1.05/1.23  thf('117', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 1.05/1.23      inference('sup-', [status(thm)], ['64', '65'])).
% 1.05/1.23  thf('118', plain,
% 1.05/1.23      (![X21 : $i, X22 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22))
% 1.05/1.23           = (k4_xboole_0 @ X21 @ X22))),
% 1.05/1.23      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.05/1.23  thf('119', plain,
% 1.05/1.23      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 1.05/1.23      inference('sup+', [status(thm)], ['117', '118'])).
% 1.05/1.23  thf('120', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.05/1.23      inference('cnf', [status(esa)], [t3_boole])).
% 1.05/1.23  thf('121', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 1.05/1.23      inference('demod', [status(thm)], ['119', '120'])).
% 1.05/1.23  thf('122', plain,
% 1.05/1.23      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 1.05/1.23           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 1.05/1.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.05/1.23  thf('123', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ sk_C_1 @ X0)
% 1.05/1.23           = (k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.05/1.23      inference('sup+', [status(thm)], ['121', '122'])).
% 1.05/1.23  thf('124', plain,
% 1.05/1.23      (((k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_D))
% 1.05/1.23         = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 1.05/1.23      inference('sup+', [status(thm)], ['116', '123'])).
% 1.05/1.23  thf('125', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 1.05/1.23      inference('demod', [status(thm)], ['119', '120'])).
% 1.05/1.23  thf('126', plain,
% 1.05/1.23      (((k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_D)) = (sk_C_1))),
% 1.05/1.23      inference('demod', [status(thm)], ['124', '125'])).
% 1.05/1.23  thf('127', plain,
% 1.05/1.23      (![X23 : $i, X24 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 1.05/1.23           = (k3_xboole_0 @ X23 @ X24))),
% 1.05/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.05/1.23  thf('128', plain,
% 1.05/1.23      (((k4_xboole_0 @ sk_C_1 @ sk_C_1)
% 1.05/1.23         = (k3_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_D)))),
% 1.05/1.23      inference('sup+', [status(thm)], ['126', '127'])).
% 1.05/1.23  thf('129', plain,
% 1.05/1.23      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['75', '76'])).
% 1.05/1.23  thf('130', plain,
% 1.05/1.23      (![X21 : $i, X22 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22))
% 1.05/1.23           = (k4_xboole_0 @ X21 @ X22))),
% 1.05/1.23      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.05/1.23  thf('131', plain,
% 1.05/1.23      (![X13 : $i, X14 : $i]:
% 1.05/1.23         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 1.05/1.23           = (k2_xboole_0 @ X13 @ X14))),
% 1.05/1.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.05/1.23  thf('132', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.05/1.23           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.05/1.23      inference('sup+', [status(thm)], ['130', '131'])).
% 1.05/1.23  thf('133', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.23  thf('134', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.05/1.23           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.05/1.23      inference('demod', [status(thm)], ['132', '133'])).
% 1.05/1.23  thf(t51_xboole_1, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.05/1.23       ( A ) ))).
% 1.05/1.23  thf('135', plain,
% 1.05/1.23      (![X28 : $i, X29 : $i]:
% 1.05/1.23         ((k2_xboole_0 @ (k3_xboole_0 @ X28 @ X29) @ (k4_xboole_0 @ X28 @ X29))
% 1.05/1.23           = (X28))),
% 1.05/1.23      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.05/1.23  thf('136', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 1.05/1.23      inference('sup+', [status(thm)], ['134', '135'])).
% 1.05/1.23  thf('137', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['129', '136'])).
% 1.05/1.23  thf('138', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['33', '34'])).
% 1.05/1.23  thf('139', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.05/1.23      inference('demod', [status(thm)], ['137', '138'])).
% 1.05/1.23  thf('140', plain,
% 1.05/1.23      (((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_D)))),
% 1.05/1.23      inference('demod', [status(thm)], ['128', '139'])).
% 1.05/1.23  thf('141', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.05/1.23           = (k4_xboole_0 @ X0 @ X1))),
% 1.05/1.23      inference('sup+', [status(thm)], ['67', '68'])).
% 1.05/1.23  thf('142', plain,
% 1.05/1.23      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_D) @ k1_xboole_0)
% 1.05/1.23         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_D) @ sk_C_1))),
% 1.05/1.23      inference('sup+', [status(thm)], ['140', '141'])).
% 1.05/1.23  thf('143', plain,
% 1.05/1.23      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 1.05/1.23           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 1.05/1.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.05/1.23  thf('144', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['31', '32'])).
% 1.05/1.23  thf('145', plain,
% 1.05/1.23      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 1.05/1.23           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 1.05/1.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.05/1.23  thf('146', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.23  thf('147', plain,
% 1.05/1.23      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 1.05/1.23      inference('demod', [status(thm)], ['15', '16'])).
% 1.05/1.23  thf('148', plain,
% 1.05/1.23      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 1.05/1.23           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 1.05/1.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.05/1.23  thf('149', plain,
% 1.05/1.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['35', '36'])).
% 1.05/1.23  thf('150', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.05/1.23           = (k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.05/1.23      inference('sup+', [status(thm)], ['148', '149'])).
% 1.05/1.23  thf('151', plain,
% 1.05/1.23      (![X13 : $i, X14 : $i]:
% 1.05/1.23         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 1.05/1.23           = (k2_xboole_0 @ X13 @ X14))),
% 1.05/1.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.05/1.23  thf('152', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))
% 1.05/1.23           = (k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.05/1.23      inference('demod', [status(thm)], ['150', '151'])).
% 1.05/1.23  thf('153', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['41', '42'])).
% 1.05/1.23  thf('154', plain,
% 1.05/1.23      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.23  thf('155', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))
% 1.05/1.23           = (k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.05/1.23      inference('demod', [status(thm)], ['152', '153', '154'])).
% 1.05/1.23  thf('156', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 1.05/1.23      inference('sup+', [status(thm)], ['134', '135'])).
% 1.05/1.23  thf('157', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((k2_xboole_0 @ k1_xboole_0 @ 
% 1.05/1.23           (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))) = (k1_xboole_0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['155', '156'])).
% 1.05/1.23  thf('158', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['33', '34'])).
% 1.05/1.23  thf('159', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.05/1.23      inference('demod', [status(thm)], ['157', '158'])).
% 1.05/1.23  thf('160', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 1.05/1.23      inference('demod', [status(thm)],
% 1.05/1.23                ['142', '143', '144', '145', '146', '147', '159'])).
% 1.05/1.23  thf('161', plain,
% 1.05/1.23      (![X28 : $i, X29 : $i]:
% 1.05/1.23         ((k2_xboole_0 @ (k3_xboole_0 @ X28 @ X29) @ (k4_xboole_0 @ X28 @ X29))
% 1.05/1.23           = (X28))),
% 1.05/1.23      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.05/1.23  thf('162', plain,
% 1.05/1.23      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_D) @ k1_xboole_0) = (sk_A))),
% 1.05/1.23      inference('sup+', [status(thm)], ['160', '161'])).
% 1.05/1.23  thf('163', plain, (((sk_D) = (k3_xboole_0 @ sk_A @ sk_D))),
% 1.05/1.23      inference('demod', [status(thm)], ['101', '102', '103'])).
% 1.05/1.23  thf('164', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['31', '32'])).
% 1.05/1.23  thf('165', plain, (((sk_D) = (sk_A))),
% 1.05/1.23      inference('demod', [status(thm)], ['162', '163', '164'])).
% 1.05/1.23  thf('166', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 1.05/1.23      inference('demod', [status(thm)], ['14', '165'])).
% 1.05/1.23  thf('167', plain,
% 1.05/1.23      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D)
% 1.05/1.23         = (k4_xboole_0 @ sk_C_1 @ sk_D))),
% 1.05/1.23      inference('sup+', [status(thm)], ['17', '18'])).
% 1.05/1.23  thf('168', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 1.05/1.23      inference('demod', [status(thm)], ['85', '86', '91'])).
% 1.05/1.23  thf('169', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ sk_C_1 @ X0)
% 1.05/1.23           = (k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.05/1.23      inference('sup+', [status(thm)], ['121', '122'])).
% 1.05/1.23  thf('170', plain,
% 1.05/1.23      (((k4_xboole_0 @ sk_C_1 @ sk_D) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 1.05/1.23      inference('sup+', [status(thm)], ['168', '169'])).
% 1.05/1.23  thf('171', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 1.05/1.23      inference('demod', [status(thm)], ['119', '120'])).
% 1.05/1.23  thf('172', plain, (((k4_xboole_0 @ sk_C_1 @ sk_D) = (sk_C_1))),
% 1.05/1.23      inference('demod', [status(thm)], ['170', '171'])).
% 1.05/1.23  thf('173', plain,
% 1.05/1.23      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D) = (sk_C_1))),
% 1.05/1.23      inference('demod', [status(thm)], ['167', '172'])).
% 1.05/1.23  thf('174', plain, (((sk_D) = (sk_A))),
% 1.05/1.23      inference('demod', [status(thm)], ['162', '163', '164'])).
% 1.05/1.23  thf('175', plain,
% 1.05/1.23      (![X16 : $i, X17 : $i]:
% 1.05/1.23         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 1.05/1.23           = (k4_xboole_0 @ X16 @ X17))),
% 1.05/1.23      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.05/1.23  thf('176', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 1.05/1.23      inference('demod', [status(thm)], ['173', '174', '175'])).
% 1.05/1.23  thf('177', plain, (((sk_B_1) = (sk_C_1))),
% 1.05/1.23      inference('sup+', [status(thm)], ['166', '176'])).
% 1.05/1.23  thf('178', plain, (((sk_C_1) != (sk_B_1))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('179', plain, ($false),
% 1.05/1.23      inference('simplify_reflect-', [status(thm)], ['177', '178'])).
% 1.05/1.23  
% 1.05/1.23  % SZS output end Refutation
% 1.05/1.23  
% 1.06/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
