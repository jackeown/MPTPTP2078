%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oeF9CU3Mth

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:00 EST 2020

% Result     : Theorem 3.89s
% Output     : Refutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 429 expanded)
%              Number of leaves         :   25 ( 149 expanded)
%              Depth                    :   17
%              Number of atoms          :  843 (3391 expanded)
%              Number of equality atoms :  108 ( 402 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','1'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','3'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','9','12'])).

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

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X26 @ X27 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('20',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ X0 )
      = ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','24'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_D ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X26 @ X27 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('40',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
    = sk_B_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X26 @ X27 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_D @ X0 ) ) )
      = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
    = sk_B_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_D @ X0 ) ) )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('51',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('53',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('57',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('60',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
    = sk_B_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('61',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X26 @ X27 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('62',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('64',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X26 @ X27 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
    = sk_D ),
    inference('sup+',[status(thm)],['60','69'])).

thf('71',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['57','58','59','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['71','72'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('74',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 = X11 )
      | ( ( k4_xboole_0 @ X12 @ X11 )
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('75',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_D )
     != k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('84',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference(demod,[status(thm)],['75','84'])).

thf('86',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['48','86'])).

thf('88',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['29','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('90',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('91',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['85'])).

thf('92',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('94',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('95',plain,(
    sk_C_1 = sk_B_1 ),
    inference(demod,[status(thm)],['88','89','92','93','94'])).

thf('96',plain,(
    sk_C_1 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oeF9CU3Mth
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.89/4.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.89/4.06  % Solved by: fo/fo7.sh
% 3.89/4.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.89/4.06  % done 5198 iterations in 3.609s
% 3.89/4.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.89/4.06  % SZS output start Refutation
% 3.89/4.06  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.89/4.06  thf(sk_B_type, type, sk_B: $i > $i).
% 3.89/4.06  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.89/4.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.89/4.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.89/4.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.89/4.06  thf(sk_A_type, type, sk_A: $i).
% 3.89/4.06  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.89/4.06  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.89/4.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.89/4.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.89/4.06  thf(sk_D_type, type, sk_D: $i).
% 3.89/4.06  thf(t72_xboole_1, conjecture,
% 3.89/4.06    (![A:$i,B:$i,C:$i,D:$i]:
% 3.89/4.06     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 3.89/4.06         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 3.89/4.06       ( ( C ) = ( B ) ) ))).
% 3.89/4.06  thf(zf_stmt_0, negated_conjecture,
% 3.89/4.06    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.89/4.06        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 3.89/4.06            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 3.89/4.06          ( ( C ) = ( B ) ) ) )),
% 3.89/4.06    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 3.89/4.06  thf('0', plain,
% 3.89/4.06      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 3.89/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.06  thf(t46_xboole_1, axiom,
% 3.89/4.06    (![A:$i,B:$i]:
% 3.89/4.06     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 3.89/4.06  thf('1', plain,
% 3.89/4.06      (![X19 : $i, X20 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 3.89/4.06      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.89/4.06  thf('2', plain,
% 3.89/4.06      (((k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 3.89/4.06      inference('sup+', [status(thm)], ['0', '1'])).
% 3.89/4.06  thf(commutativity_k2_xboole_0, axiom,
% 3.89/4.06    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.89/4.06  thf('3', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.89/4.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.89/4.06  thf('4', plain,
% 3.89/4.06      (((k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B_1 @ sk_A)) = (k1_xboole_0))),
% 3.89/4.06      inference('demod', [status(thm)], ['2', '3'])).
% 3.89/4.06  thf(t41_xboole_1, axiom,
% 3.89/4.06    (![A:$i,B:$i,C:$i]:
% 3.89/4.06     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.89/4.06       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.89/4.06  thf('5', plain,
% 3.89/4.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 3.89/4.06           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.89/4.06      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.89/4.06  thf(t39_xboole_1, axiom,
% 3.89/4.06    (![A:$i,B:$i]:
% 3.89/4.06     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.89/4.06  thf('6', plain,
% 3.89/4.06      (![X13 : $i, X14 : $i]:
% 3.89/4.06         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 3.89/4.06           = (k2_xboole_0 @ X13 @ X14))),
% 3.89/4.06      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.89/4.06  thf('7', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.06         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.89/4.06           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 3.89/4.06      inference('sup+', [status(thm)], ['5', '6'])).
% 3.89/4.06  thf('8', plain,
% 3.89/4.06      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 3.89/4.06         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C_1 @ sk_B_1)))),
% 3.89/4.06      inference('sup+', [status(thm)], ['4', '7'])).
% 3.89/4.06  thf('9', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.89/4.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.89/4.06  thf('10', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.89/4.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.89/4.06  thf(t1_boole, axiom,
% 3.89/4.06    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.89/4.06  thf('11', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 3.89/4.06      inference('cnf', [status(esa)], [t1_boole])).
% 3.89/4.06  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.89/4.06      inference('sup+', [status(thm)], ['10', '11'])).
% 3.89/4.06  thf('13', plain,
% 3.89/4.06      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C_1 @ sk_B_1)))),
% 3.89/4.06      inference('demod', [status(thm)], ['8', '9', '12'])).
% 3.89/4.06  thf('14', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 3.89/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.06  thf(t7_xboole_0, axiom,
% 3.89/4.06    (![A:$i]:
% 3.89/4.06     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.89/4.06          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 3.89/4.06  thf('15', plain,
% 3.89/4.06      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 3.89/4.06      inference('cnf', [status(esa)], [t7_xboole_0])).
% 3.89/4.06  thf(t4_xboole_0, axiom,
% 3.89/4.06    (![A:$i,B:$i]:
% 3.89/4.06     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 3.89/4.06            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.89/4.06       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.89/4.06            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 3.89/4.06  thf('16', plain,
% 3.89/4.06      (![X4 : $i, X6 : $i, X7 : $i]:
% 3.89/4.06         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 3.89/4.06          | ~ (r1_xboole_0 @ X4 @ X7))),
% 3.89/4.06      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.89/4.06  thf('17', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]:
% 3.89/4.06         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 3.89/4.06      inference('sup-', [status(thm)], ['15', '16'])).
% 3.89/4.06  thf('18', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 3.89/4.06      inference('sup-', [status(thm)], ['14', '17'])).
% 3.89/4.06  thf(t51_xboole_1, axiom,
% 3.89/4.06    (![A:$i,B:$i]:
% 3.89/4.06     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 3.89/4.06       ( A ) ))).
% 3.89/4.06  thf('19', plain,
% 3.89/4.06      (![X26 : $i, X27 : $i]:
% 3.89/4.06         ((k2_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ (k4_xboole_0 @ X26 @ X27))
% 3.89/4.06           = (X26))),
% 3.89/4.06      inference('cnf', [status(esa)], [t51_xboole_1])).
% 3.89/4.06  thf('20', plain,
% 3.89/4.06      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_A)) = (sk_C_1))),
% 3.89/4.06      inference('sup+', [status(thm)], ['18', '19'])).
% 3.89/4.06  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.89/4.06      inference('sup+', [status(thm)], ['10', '11'])).
% 3.89/4.06  thf('22', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 3.89/4.06      inference('demod', [status(thm)], ['20', '21'])).
% 3.89/4.06  thf('23', plain,
% 3.89/4.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 3.89/4.06           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.89/4.06      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.89/4.06  thf('24', plain,
% 3.89/4.06      (![X0 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ sk_C_1 @ X0)
% 3.89/4.06           = (k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 3.89/4.06      inference('sup+', [status(thm)], ['22', '23'])).
% 3.89/4.06  thf('25', plain,
% 3.89/4.06      (((k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_C_1 @ sk_B_1))
% 3.89/4.06         = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 3.89/4.06      inference('sup+', [status(thm)], ['13', '24'])).
% 3.89/4.06  thf(t48_xboole_1, axiom,
% 3.89/4.06    (![A:$i,B:$i]:
% 3.89/4.06     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.89/4.06  thf('26', plain,
% 3.89/4.06      (![X21 : $i, X22 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 3.89/4.06           = (k3_xboole_0 @ X21 @ X22))),
% 3.89/4.06      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.89/4.06  thf(commutativity_k3_xboole_0, axiom,
% 3.89/4.06    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.89/4.06  thf('27', plain,
% 3.89/4.06      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 3.89/4.06      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.89/4.06  thf('28', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 3.89/4.06      inference('demod', [status(thm)], ['20', '21'])).
% 3.89/4.06  thf('29', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 3.89/4.06      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 3.89/4.06  thf('30', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 3.89/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.06  thf('31', plain,
% 3.89/4.06      (![X4 : $i, X5 : $i]:
% 3.89/4.06         ((r1_xboole_0 @ X4 @ X5)
% 3.89/4.06          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 3.89/4.06      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.89/4.06  thf('32', plain,
% 3.89/4.06      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 3.89/4.06      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.89/4.06  thf('33', plain,
% 3.89/4.06      (![X4 : $i, X6 : $i, X7 : $i]:
% 3.89/4.06         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 3.89/4.06          | ~ (r1_xboole_0 @ X4 @ X7))),
% 3.89/4.06      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.89/4.06  thf('34', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.06         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.89/4.06          | ~ (r1_xboole_0 @ X0 @ X1))),
% 3.89/4.06      inference('sup-', [status(thm)], ['32', '33'])).
% 3.89/4.06  thf('35', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]:
% 3.89/4.06         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 3.89/4.06      inference('sup-', [status(thm)], ['31', '34'])).
% 3.89/4.06  thf('36', plain, ((r1_xboole_0 @ sk_B_1 @ sk_D)),
% 3.89/4.06      inference('sup-', [status(thm)], ['30', '35'])).
% 3.89/4.06  thf('37', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]:
% 3.89/4.06         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 3.89/4.06      inference('sup-', [status(thm)], ['15', '16'])).
% 3.89/4.06  thf('38', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 3.89/4.06      inference('sup-', [status(thm)], ['36', '37'])).
% 3.89/4.06  thf('39', plain,
% 3.89/4.06      (![X26 : $i, X27 : $i]:
% 3.89/4.06         ((k2_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ (k4_xboole_0 @ X26 @ X27))
% 3.89/4.06           = (X26))),
% 3.89/4.06      inference('cnf', [status(esa)], [t51_xboole_1])).
% 3.89/4.06  thf('40', plain,
% 3.89/4.06      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_D)) = (sk_B_1))),
% 3.89/4.06      inference('sup+', [status(thm)], ['38', '39'])).
% 3.89/4.06  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.89/4.06      inference('sup+', [status(thm)], ['10', '11'])).
% 3.89/4.06  thf('42', plain, (((k4_xboole_0 @ sk_B_1 @ sk_D) = (sk_B_1))),
% 3.89/4.06      inference('demod', [status(thm)], ['40', '41'])).
% 3.89/4.06  thf('43', plain,
% 3.89/4.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 3.89/4.06           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.89/4.06      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.89/4.06  thf('44', plain,
% 3.89/4.06      (![X26 : $i, X27 : $i]:
% 3.89/4.06         ((k2_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ (k4_xboole_0 @ X26 @ X27))
% 3.89/4.06           = (X26))),
% 3.89/4.06      inference('cnf', [status(esa)], [t51_xboole_1])).
% 3.89/4.06  thf('45', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.06         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 3.89/4.06           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.89/4.06           = (k4_xboole_0 @ X2 @ X1))),
% 3.89/4.06      inference('sup+', [status(thm)], ['43', '44'])).
% 3.89/4.06  thf('46', plain,
% 3.89/4.06      (![X0 : $i]:
% 3.89/4.06         ((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ X0) @ 
% 3.89/4.06           (k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_D @ X0)))
% 3.89/4.06           = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 3.89/4.06      inference('sup+', [status(thm)], ['42', '45'])).
% 3.89/4.06  thf('47', plain, (((k4_xboole_0 @ sk_B_1 @ sk_D) = (sk_B_1))),
% 3.89/4.06      inference('demod', [status(thm)], ['40', '41'])).
% 3.89/4.06  thf('48', plain,
% 3.89/4.06      (![X0 : $i]:
% 3.89/4.06         ((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ X0) @ 
% 3.89/4.06           (k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_D @ X0))) = (sk_B_1))),
% 3.89/4.06      inference('demod', [status(thm)], ['46', '47'])).
% 3.89/4.06  thf('49', plain,
% 3.89/4.06      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 3.89/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.06  thf('50', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.89/4.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.89/4.06  thf('51', plain,
% 3.89/4.06      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 3.89/4.06      inference('demod', [status(thm)], ['49', '50'])).
% 3.89/4.06  thf('52', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.89/4.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.89/4.06  thf('53', plain,
% 3.89/4.06      (![X19 : $i, X20 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 3.89/4.06      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.89/4.06  thf('54', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.89/4.06      inference('sup+', [status(thm)], ['52', '53'])).
% 3.89/4.06  thf('55', plain,
% 3.89/4.06      (((k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)) = (k1_xboole_0))),
% 3.89/4.06      inference('sup+', [status(thm)], ['51', '54'])).
% 3.89/4.06  thf('56', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.06         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.89/4.06           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 3.89/4.06      inference('sup+', [status(thm)], ['5', '6'])).
% 3.89/4.06  thf('57', plain,
% 3.89/4.06      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 3.89/4.06         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B_1)))),
% 3.89/4.06      inference('sup+', [status(thm)], ['55', '56'])).
% 3.89/4.06  thf('58', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.89/4.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.89/4.06  thf('59', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.89/4.06      inference('sup+', [status(thm)], ['10', '11'])).
% 3.89/4.06  thf('60', plain, (((k4_xboole_0 @ sk_B_1 @ sk_D) = (sk_B_1))),
% 3.89/4.06      inference('demod', [status(thm)], ['40', '41'])).
% 3.89/4.06  thf('61', plain,
% 3.89/4.06      (![X26 : $i, X27 : $i]:
% 3.89/4.06         ((k2_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ (k4_xboole_0 @ X26 @ X27))
% 3.89/4.06           = (X26))),
% 3.89/4.06      inference('cnf', [status(esa)], [t51_xboole_1])).
% 3.89/4.06  thf('62', plain,
% 3.89/4.06      (![X19 : $i, X20 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 3.89/4.06      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.89/4.06  thf('63', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 3.89/4.06      inference('sup+', [status(thm)], ['61', '62'])).
% 3.89/4.06  thf(t49_xboole_1, axiom,
% 3.89/4.06    (![A:$i,B:$i,C:$i]:
% 3.89/4.06     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 3.89/4.06       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 3.89/4.06  thf('64', plain,
% 3.89/4.06      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.89/4.06         ((k3_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 3.89/4.06           = (k4_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ X25))),
% 3.89/4.06      inference('cnf', [status(esa)], [t49_xboole_1])).
% 3.89/4.06  thf('65', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]:
% 3.89/4.06         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.89/4.06      inference('demod', [status(thm)], ['63', '64'])).
% 3.89/4.06  thf('66', plain,
% 3.89/4.06      (![X26 : $i, X27 : $i]:
% 3.89/4.06         ((k2_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ (k4_xboole_0 @ X26 @ X27))
% 3.89/4.06           = (X26))),
% 3.89/4.06      inference('cnf', [status(esa)], [t51_xboole_1])).
% 3.89/4.06  thf('67', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]:
% 3.89/4.06         ((k2_xboole_0 @ k1_xboole_0 @ 
% 3.89/4.06           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))) = (X0))),
% 3.89/4.06      inference('sup+', [status(thm)], ['65', '66'])).
% 3.89/4.06  thf('68', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.89/4.06      inference('sup+', [status(thm)], ['10', '11'])).
% 3.89/4.06  thf('69', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 3.89/4.06      inference('demod', [status(thm)], ['67', '68'])).
% 3.89/4.06  thf('70', plain, (((k4_xboole_0 @ sk_D @ sk_B_1) = (sk_D))),
% 3.89/4.06      inference('sup+', [status(thm)], ['60', '69'])).
% 3.89/4.06  thf('71', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 3.89/4.06      inference('demod', [status(thm)], ['57', '58', '59', '70'])).
% 3.89/4.06  thf('72', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.89/4.06      inference('sup+', [status(thm)], ['52', '53'])).
% 3.89/4.06  thf('73', plain, (((k4_xboole_0 @ sk_D @ sk_A) = (k1_xboole_0))),
% 3.89/4.06      inference('sup+', [status(thm)], ['71', '72'])).
% 3.89/4.06  thf(t32_xboole_1, axiom,
% 3.89/4.06    (![A:$i,B:$i]:
% 3.89/4.06     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 3.89/4.06       ( ( A ) = ( B ) ) ))).
% 3.89/4.06  thf('74', plain,
% 3.89/4.06      (![X11 : $i, X12 : $i]:
% 3.89/4.06         (((X12) = (X11))
% 3.89/4.06          | ((k4_xboole_0 @ X12 @ X11) != (k4_xboole_0 @ X11 @ X12)))),
% 3.89/4.06      inference('cnf', [status(esa)], [t32_xboole_1])).
% 3.89/4.06  thf('75', plain,
% 3.89/4.06      ((((k4_xboole_0 @ sk_A @ sk_D) != (k1_xboole_0)) | ((sk_A) = (sk_D)))),
% 3.89/4.06      inference('sup-', [status(thm)], ['73', '74'])).
% 3.89/4.06  thf('76', plain,
% 3.89/4.06      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 3.89/4.06      inference('demod', [status(thm)], ['49', '50'])).
% 3.89/4.06  thf('77', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 3.89/4.06      inference('demod', [status(thm)], ['20', '21'])).
% 3.89/4.06  thf('78', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 3.89/4.06      inference('demod', [status(thm)], ['67', '68'])).
% 3.89/4.06  thf('79', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 3.89/4.06      inference('sup+', [status(thm)], ['77', '78'])).
% 3.89/4.06  thf('80', plain,
% 3.89/4.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 3.89/4.06           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.89/4.06      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.89/4.06  thf('81', plain,
% 3.89/4.06      (![X0 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ sk_A @ X0)
% 3.89/4.06           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 3.89/4.06      inference('sup+', [status(thm)], ['79', '80'])).
% 3.89/4.06  thf('82', plain,
% 3.89/4.06      (((k4_xboole_0 @ sk_A @ sk_D)
% 3.89/4.06         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 3.89/4.06      inference('sup+', [status(thm)], ['76', '81'])).
% 3.89/4.06  thf('83', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.89/4.06      inference('sup+', [status(thm)], ['52', '53'])).
% 3.89/4.06  thf('84', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 3.89/4.06      inference('demod', [status(thm)], ['82', '83'])).
% 3.89/4.06  thf('85', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (sk_D)))),
% 3.89/4.06      inference('demod', [status(thm)], ['75', '84'])).
% 3.89/4.06  thf('86', plain, (((sk_A) = (sk_D))),
% 3.89/4.06      inference('simplify', [status(thm)], ['85'])).
% 3.89/4.06  thf('87', plain,
% 3.89/4.06      (![X0 : $i]:
% 3.89/4.06         ((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ X0) @ 
% 3.89/4.06           (k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_A @ X0))) = (sk_B_1))),
% 3.89/4.06      inference('demod', [status(thm)], ['48', '86'])).
% 3.89/4.06  thf('88', plain,
% 3.89/4.06      (((k2_xboole_0 @ sk_C_1 @ 
% 3.89/4.06         (k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_A @ sk_C_1))) = (sk_B_1))),
% 3.89/4.06      inference('sup+', [status(thm)], ['29', '87'])).
% 3.89/4.06  thf('89', plain,
% 3.89/4.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.89/4.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.89/4.06  thf('90', plain,
% 3.89/4.06      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 3.89/4.06      inference('demod', [status(thm)], ['49', '50'])).
% 3.89/4.06  thf('91', plain, (((sk_A) = (sk_D))),
% 3.89/4.06      inference('simplify', [status(thm)], ['85'])).
% 3.89/4.06  thf('92', plain,
% 3.89/4.06      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 3.89/4.06      inference('demod', [status(thm)], ['90', '91'])).
% 3.89/4.06  thf('93', plain,
% 3.89/4.06      (![X19 : $i, X20 : $i]:
% 3.89/4.06         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 3.89/4.06      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.89/4.06  thf('94', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 3.89/4.06      inference('cnf', [status(esa)], [t1_boole])).
% 3.89/4.06  thf('95', plain, (((sk_C_1) = (sk_B_1))),
% 3.89/4.06      inference('demod', [status(thm)], ['88', '89', '92', '93', '94'])).
% 3.89/4.06  thf('96', plain, (((sk_C_1) != (sk_B_1))),
% 3.89/4.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.06  thf('97', plain, ($false),
% 3.89/4.06      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 3.89/4.06  
% 3.89/4.06  % SZS output end Refutation
% 3.89/4.06  
% 3.89/4.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
