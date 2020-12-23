%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1XYbe2bnfd

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:57 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 763 expanded)
%              Number of leaves         :   24 ( 265 expanded)
%              Depth                    :   16
%              Number of atoms          :  883 (5873 expanded)
%              Number of equality atoms :  114 ( 717 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
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
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['7','19'])).

thf('21',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('23',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','18'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['22','38'])).

thf('40',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('49',plain,
    ( ( k2_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('52',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('55',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['49','50','53','54'])).

thf('56',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('57',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('58',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_C @ sk_D ) )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('61',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('63',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('65',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('67',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('68',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('70',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('73',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('76',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('80',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['82'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('84',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('85',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('87',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('93',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['73','93'])).

thf('95',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['55','94'])).

thf('96',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('97',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['55','94'])).

thf('98',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('99',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['4','95','96','97','98'])).

thf('100',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['85','90'])).

thf('101',plain,(
    sk_A = sk_D ),
    inference('sup+',[status(thm)],['55','94'])).

thf('102',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    sk_B = sk_C ),
    inference('sup+',[status(thm)],['99','102'])).

thf('104',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['103','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1XYbe2bnfd
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:08:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.56/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.56/0.75  % Solved by: fo/fo7.sh
% 0.56/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.75  % done 671 iterations in 0.302s
% 0.56/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.56/0.75  % SZS output start Refutation
% 0.56/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.56/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.75  thf(sk_D_type, type, sk_D: $i).
% 0.56/0.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.56/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.56/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.56/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.75  thf(t72_xboole_1, conjecture,
% 0.56/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.75     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.56/0.75         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.56/0.75       ( ( C ) = ( B ) ) ))).
% 0.56/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.75    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.75        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.56/0.75            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.56/0.75          ( ( C ) = ( B ) ) ) )),
% 0.56/0.75    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.56/0.75  thf('0', plain,
% 0.56/0.75      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(commutativity_k2_xboole_0, axiom,
% 0.56/0.75    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.56/0.75  thf('1', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.56/0.75  thf('2', plain,
% 0.56/0.75      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.56/0.75      inference('demod', [status(thm)], ['0', '1'])).
% 0.56/0.75  thf(t40_xboole_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.56/0.75  thf('3', plain,
% 0.56/0.75      (![X20 : $i, X21 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.56/0.75           = (k4_xboole_0 @ X20 @ X21))),
% 0.56/0.75      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.56/0.75  thf('4', plain,
% 0.56/0.75      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 0.56/0.75         = (k4_xboole_0 @ sk_C @ sk_D))),
% 0.56/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.56/0.75  thf('5', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(d7_xboole_0, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.56/0.75       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.56/0.75  thf('6', plain,
% 0.56/0.75      (![X4 : $i, X5 : $i]:
% 0.56/0.75         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.56/0.75      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.56/0.75  thf('7', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.56/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.75  thf(t48_xboole_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.56/0.75  thf('8', plain,
% 0.56/0.75      (![X25 : $i, X26 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.56/0.75           = (k3_xboole_0 @ X25 @ X26))),
% 0.56/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.56/0.75  thf('9', plain,
% 0.56/0.75      (![X25 : $i, X26 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.56/0.75           = (k3_xboole_0 @ X25 @ X26))),
% 0.56/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.56/0.75  thf('10', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.56/0.75           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.56/0.75      inference('sup+', [status(thm)], ['8', '9'])).
% 0.56/0.75  thf(t36_xboole_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.56/0.75  thf('11', plain,
% 0.56/0.75      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.56/0.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.56/0.75  thf(l32_xboole_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.56/0.75  thf('12', plain,
% 0.56/0.75      (![X8 : $i, X10 : $i]:
% 0.56/0.75         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.56/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.56/0.75  thf('13', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.56/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.56/0.75  thf('14', plain,
% 0.56/0.75      (![X25 : $i, X26 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.56/0.75           = (k3_xboole_0 @ X25 @ X26))),
% 0.56/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.56/0.75  thf('15', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.56/0.75           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.56/0.75      inference('sup+', [status(thm)], ['13', '14'])).
% 0.56/0.75  thf(t3_boole, axiom,
% 0.56/0.75    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.56/0.75  thf('16', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.56/0.75      inference('cnf', [status(esa)], [t3_boole])).
% 0.56/0.75  thf(commutativity_k3_xboole_0, axiom,
% 0.56/0.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.56/0.75  thf('17', plain,
% 0.56/0.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.56/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.56/0.75  thf('18', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ X0 @ X1)
% 0.56/0.75           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.56/0.75      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.56/0.75  thf('19', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.56/0.75           = (k4_xboole_0 @ X1 @ X0))),
% 0.56/0.75      inference('demod', [status(thm)], ['10', '18'])).
% 0.56/0.75  thf('20', plain,
% 0.56/0.75      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.56/0.75      inference('sup+', [status(thm)], ['7', '19'])).
% 0.56/0.75  thf('21', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.56/0.75      inference('cnf', [status(esa)], [t3_boole])).
% 0.56/0.75  thf('22', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.56/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.56/0.75  thf(idempotence_k2_xboole_0, axiom,
% 0.56/0.75    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.56/0.75  thf('23', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 0.56/0.75      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.56/0.75  thf(t41_xboole_1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.56/0.75       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.56/0.75  thf('24', plain,
% 0.56/0.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.56/0.75           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.56/0.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.56/0.75  thf('25', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.56/0.75           = (k4_xboole_0 @ X1 @ X0))),
% 0.56/0.75      inference('sup+', [status(thm)], ['23', '24'])).
% 0.56/0.75  thf('26', plain,
% 0.56/0.75      (![X25 : $i, X26 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.56/0.75           = (k3_xboole_0 @ X25 @ X26))),
% 0.56/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.56/0.75  thf('27', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.56/0.75           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.56/0.75      inference('sup+', [status(thm)], ['25', '26'])).
% 0.56/0.75  thf('28', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.56/0.75      inference('cnf', [status(esa)], [t3_boole])).
% 0.56/0.75  thf('29', plain,
% 0.56/0.75      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.56/0.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.56/0.75  thf('30', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.56/0.75      inference('sup+', [status(thm)], ['28', '29'])).
% 0.56/0.75  thf('31', plain,
% 0.56/0.75      (![X8 : $i, X10 : $i]:
% 0.56/0.75         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.56/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.56/0.75  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.56/0.75      inference('sup-', [status(thm)], ['30', '31'])).
% 0.56/0.75  thf('33', plain,
% 0.56/0.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.56/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.56/0.75  thf('34', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.56/0.75      inference('demod', [status(thm)], ['27', '32', '33'])).
% 0.56/0.75  thf('35', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.56/0.75           = (k4_xboole_0 @ X1 @ X0))),
% 0.56/0.75      inference('demod', [status(thm)], ['10', '18'])).
% 0.56/0.75  thf('36', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.56/0.75           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.56/0.75      inference('sup+', [status(thm)], ['34', '35'])).
% 0.56/0.75  thf('37', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.56/0.75      inference('cnf', [status(esa)], [t3_boole])).
% 0.56/0.75  thf('38', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.56/0.75      inference('demod', [status(thm)], ['36', '37'])).
% 0.56/0.75  thf('39', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.56/0.75      inference('sup+', [status(thm)], ['22', '38'])).
% 0.56/0.75  thf('40', plain,
% 0.56/0.75      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.56/0.75      inference('demod', [status(thm)], ['0', '1'])).
% 0.56/0.75  thf('41', plain,
% 0.56/0.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.56/0.75           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.56/0.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.56/0.75  thf('42', plain,
% 0.56/0.75      (![X0 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 0.56/0.75           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.56/0.75      inference('sup+', [status(thm)], ['40', '41'])).
% 0.56/0.75  thf('43', plain,
% 0.56/0.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.56/0.75           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.56/0.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.56/0.75  thf('44', plain,
% 0.56/0.75      (![X0 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 0.56/0.75           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.56/0.75      inference('demod', [status(thm)], ['42', '43'])).
% 0.56/0.75  thf('45', plain,
% 0.56/0.75      (((k4_xboole_0 @ sk_A @ sk_D)
% 0.56/0.75         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.56/0.75      inference('sup+', [status(thm)], ['39', '44'])).
% 0.56/0.75  thf('46', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.56/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.56/0.75  thf('47', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 0.56/0.75      inference('demod', [status(thm)], ['45', '46'])).
% 0.56/0.75  thf(t39_xboole_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.56/0.75  thf('48', plain,
% 0.56/0.75      (![X17 : $i, X18 : $i]:
% 0.56/0.75         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.56/0.75           = (k2_xboole_0 @ X17 @ X18))),
% 0.56/0.75      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.56/0.75  thf('49', plain,
% 0.56/0.75      (((k2_xboole_0 @ sk_D @ k1_xboole_0) = (k2_xboole_0 @ sk_D @ sk_A))),
% 0.56/0.75      inference('sup+', [status(thm)], ['47', '48'])).
% 0.56/0.75  thf('50', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.56/0.75  thf('51', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.56/0.75  thf(t1_boole, axiom,
% 0.56/0.75    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.56/0.75  thf('52', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.56/0.75      inference('cnf', [status(esa)], [t1_boole])).
% 0.56/0.75  thf('53', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.56/0.75      inference('sup+', [status(thm)], ['51', '52'])).
% 0.56/0.75  thf('54', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.56/0.75  thf('55', plain, (((sk_D) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.56/0.75      inference('demod', [status(thm)], ['49', '50', '53', '54'])).
% 0.56/0.75  thf('56', plain,
% 0.56/0.75      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 0.56/0.75         = (k4_xboole_0 @ sk_C @ sk_D))),
% 0.56/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.56/0.75  thf('57', plain,
% 0.56/0.75      (![X17 : $i, X18 : $i]:
% 0.56/0.75         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.56/0.75           = (k2_xboole_0 @ X17 @ X18))),
% 0.56/0.75      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.56/0.75  thf('58', plain,
% 0.56/0.75      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_C @ sk_D))
% 0.56/0.75         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.56/0.75      inference('sup+', [status(thm)], ['56', '57'])).
% 0.56/0.75  thf('59', plain,
% 0.56/0.75      (![X17 : $i, X18 : $i]:
% 0.56/0.75         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.56/0.75           = (k2_xboole_0 @ X17 @ X18))),
% 0.56/0.75      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.56/0.75  thf('60', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.56/0.75  thf('61', plain,
% 0.56/0.75      (((k2_xboole_0 @ sk_C @ sk_D)
% 0.56/0.75         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.56/0.75      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.56/0.75  thf('62', plain,
% 0.56/0.75      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.56/0.75      inference('demod', [status(thm)], ['0', '1'])).
% 0.56/0.75  thf('63', plain,
% 0.56/0.75      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.56/0.75         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.56/0.75      inference('demod', [status(thm)], ['61', '62'])).
% 0.56/0.75  thf('64', plain,
% 0.56/0.75      (![X20 : $i, X21 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.56/0.75           = (k4_xboole_0 @ X20 @ X21))),
% 0.56/0.75      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.56/0.75  thf('65', plain,
% 0.56/0.75      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 0.56/0.75         (k2_xboole_0 @ sk_B @ sk_A))
% 0.56/0.75         = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.56/0.75      inference('sup+', [status(thm)], ['63', '64'])).
% 0.56/0.75  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.56/0.75      inference('sup-', [status(thm)], ['30', '31'])).
% 0.56/0.75  thf('67', plain,
% 0.56/0.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 0.56/0.75           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.56/0.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.56/0.75  thf('68', plain,
% 0.56/0.75      (((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A))),
% 0.56/0.75      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.56/0.75  thf('69', plain,
% 0.56/0.75      (![X17 : $i, X18 : $i]:
% 0.56/0.75         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.56/0.75           = (k2_xboole_0 @ X17 @ X18))),
% 0.56/0.75      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.56/0.75  thf('70', plain,
% 0.56/0.75      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 0.56/0.75         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)))),
% 0.56/0.75      inference('sup+', [status(thm)], ['68', '69'])).
% 0.56/0.75  thf('71', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.56/0.75  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.56/0.75      inference('sup+', [status(thm)], ['51', '52'])).
% 0.56/0.75  thf('73', plain,
% 0.56/0.75      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)))),
% 0.56/0.75      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.56/0.75  thf('74', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('75', plain,
% 0.56/0.75      (![X4 : $i, X5 : $i]:
% 0.56/0.75         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.56/0.75      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.56/0.75  thf('76', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.56/0.75      inference('sup-', [status(thm)], ['74', '75'])).
% 0.56/0.75  thf('77', plain,
% 0.56/0.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.56/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.56/0.75  thf('78', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.56/0.75      inference('demod', [status(thm)], ['76', '77'])).
% 0.56/0.75  thf('79', plain,
% 0.56/0.75      (![X25 : $i, X26 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.56/0.75           = (k3_xboole_0 @ X25 @ X26))),
% 0.56/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.56/0.75  thf('80', plain,
% 0.56/0.75      (![X8 : $i, X9 : $i]:
% 0.56/0.75         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 0.56/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.56/0.75  thf('81', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.56/0.75          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['79', '80'])).
% 0.56/0.75  thf('82', plain,
% 0.56/0.75      ((((k1_xboole_0) != (k1_xboole_0))
% 0.56/0.75        | (r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ sk_D)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['78', '81'])).
% 0.56/0.75  thf('83', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ sk_D))),
% 0.56/0.75      inference('simplify', [status(thm)], ['82'])).
% 0.56/0.75  thf(t12_xboole_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.56/0.75  thf('84', plain,
% 0.56/0.75      (![X11 : $i, X12 : $i]:
% 0.56/0.75         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.56/0.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.56/0.75  thf('85', plain,
% 0.56/0.75      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_D))
% 0.56/0.75         = (k4_xboole_0 @ sk_B @ sk_D))),
% 0.56/0.75      inference('sup-', [status(thm)], ['83', '84'])).
% 0.56/0.75  thf('86', plain,
% 0.56/0.75      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.56/0.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.56/0.75  thf('87', plain,
% 0.56/0.75      (![X11 : $i, X12 : $i]:
% 0.56/0.75         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.56/0.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.56/0.75  thf('88', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.56/0.75      inference('sup-', [status(thm)], ['86', '87'])).
% 0.56/0.75  thf('89', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.56/0.75  thf('90', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.56/0.75      inference('demod', [status(thm)], ['88', '89'])).
% 0.56/0.75  thf('91', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_D))),
% 0.56/0.75      inference('demod', [status(thm)], ['85', '90'])).
% 0.56/0.75  thf('92', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.56/0.75      inference('demod', [status(thm)], ['36', '37'])).
% 0.56/0.75  thf('93', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 0.56/0.75      inference('sup+', [status(thm)], ['91', '92'])).
% 0.56/0.75  thf('94', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.56/0.75      inference('demod', [status(thm)], ['73', '93'])).
% 0.56/0.75  thf('95', plain, (((sk_A) = (sk_D))),
% 0.56/0.75      inference('sup+', [status(thm)], ['55', '94'])).
% 0.56/0.75  thf('96', plain,
% 0.56/0.75      (![X20 : $i, X21 : $i]:
% 0.56/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.56/0.75           = (k4_xboole_0 @ X20 @ X21))),
% 0.56/0.75      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.56/0.75  thf('97', plain, (((sk_A) = (sk_D))),
% 0.56/0.75      inference('sup+', [status(thm)], ['55', '94'])).
% 0.56/0.75  thf('98', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.56/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.56/0.75  thf('99', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 0.56/0.75      inference('demod', [status(thm)], ['4', '95', '96', '97', '98'])).
% 0.56/0.75  thf('100', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_D))),
% 0.56/0.75      inference('demod', [status(thm)], ['85', '90'])).
% 0.56/0.75  thf('101', plain, (((sk_A) = (sk_D))),
% 0.56/0.75      inference('sup+', [status(thm)], ['55', '94'])).
% 0.56/0.75  thf('102', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.56/0.75      inference('demod', [status(thm)], ['100', '101'])).
% 0.56/0.75  thf('103', plain, (((sk_B) = (sk_C))),
% 0.56/0.75      inference('sup+', [status(thm)], ['99', '102'])).
% 0.56/0.75  thf('104', plain, (((sk_C) != (sk_B))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('105', plain, ($false),
% 0.56/0.75      inference('simplify_reflect-', [status(thm)], ['103', '104'])).
% 0.56/0.75  
% 0.56/0.75  % SZS output end Refutation
% 0.56/0.75  
% 0.56/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
