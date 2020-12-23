%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GJhMZ1seKo

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:03 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  136 (1024 expanded)
%              Number of leaves         :   25 ( 359 expanded)
%              Depth                    :   16
%              Number of atoms          :  955 (8801 expanded)
%              Number of equality atoms :  115 (1008 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
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

thf('4',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('9',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['11','12'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k2_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36','39'])).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('43',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('46',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','47','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','49'])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_D @ sk_A ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('58',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_C_1 )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('61',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('63',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ sk_A )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('69',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','47','48'])).

thf('72',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('76',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) )
    = sk_D ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
    = sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['67','70','71','78'])).

thf('80',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('81',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('84',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','49'])).

thf('87',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('88',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['54','55','84','85','86','87'])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','88'])).

thf('90',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('91',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('93',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('94',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['54','55','84','85','86','87'])).

thf('96',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('97',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['54','55','84','85','86','87'])).

thf('98',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('100',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('102',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('104',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['94','95','96','97','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('107',plain,(
    sk_C_1 = sk_B_1 ),
    inference(demod,[status(thm)],['91','105','106'])).

thf('108',plain,(
    sk_C_1 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GJhMZ1seKo
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:35:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.62  % Solved by: fo/fo7.sh
% 0.37/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.62  % done 257 iterations in 0.158s
% 0.37/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.62  % SZS output start Refutation
% 0.37/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.62  thf(t72_xboole_1, conjecture,
% 0.37/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.62     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.37/0.62         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.37/0.62       ( ( C ) = ( B ) ) ))).
% 0.37/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.62        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.37/0.62            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.37/0.62          ( ( C ) = ( B ) ) ) )),
% 0.37/0.62    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.37/0.62  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(symmetry_r1_xboole_0, axiom,
% 0.37/0.62    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.37/0.62  thf('1', plain,
% 0.37/0.62      (![X3 : $i, X4 : $i]:
% 0.37/0.62         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.37/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.62  thf('2', plain, ((r1_xboole_0 @ sk_B_1 @ sk_D)),
% 0.37/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.62  thf(t7_xboole_0, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.62  thf('3', plain,
% 0.37/0.62      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.37/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.62  thf(t4_xboole_0, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.62            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.62  thf('4', plain,
% 0.37/0.62      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.37/0.62         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.37/0.62          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.37/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.62  thf('5', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.62  thf('6', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['2', '5'])).
% 0.37/0.62  thf('7', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('8', plain,
% 0.37/0.62      (![X3 : $i, X4 : $i]:
% 0.37/0.62         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.37/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.62  thf('9', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.37/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.62  thf('10', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.62  thf('11', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.62  thf(t51_xboole_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.37/0.62       ( A ) ))).
% 0.37/0.62  thf('12', plain,
% 0.37/0.62      (![X25 : $i, X26 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ (k4_xboole_0 @ X25 @ X26))
% 0.37/0.62           = (X25))),
% 0.37/0.62      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.37/0.62  thf('13', plain,
% 0.37/0.62      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_1)) = (sk_A))),
% 0.37/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.62  thf(commutativity_k2_xboole_0, axiom,
% 0.37/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.37/0.62  thf('14', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.62  thf(t1_boole, axiom,
% 0.37/0.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.62  thf('15', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.37/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.62  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf('17', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['13', '16'])).
% 0.37/0.62  thf('18', plain,
% 0.37/0.62      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('19', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.62  thf('20', plain,
% 0.37/0.62      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.62  thf(t41_xboole_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.62       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.62  thf('21', plain,
% 0.37/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.37/0.62           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.37/0.62  thf('22', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D)
% 0.37/0.62           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['20', '21'])).
% 0.37/0.62  thf('23', plain,
% 0.37/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.37/0.62           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.37/0.62  thf('24', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D)
% 0.37/0.62           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B_1) @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.62  thf('25', plain,
% 0.37/0.62      (((k4_xboole_0 @ sk_A @ sk_D)
% 0.37/0.62         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ sk_A))),
% 0.37/0.62      inference('sup+', [status(thm)], ['17', '24'])).
% 0.37/0.62  thf(t40_xboole_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.62  thf('26', plain,
% 0.37/0.62      (![X15 : $i, X16 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.37/0.62           = (k4_xboole_0 @ X15 @ X16))),
% 0.37/0.62      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.37/0.62  thf(t39_xboole_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.62  thf('27', plain,
% 0.37/0.62      (![X12 : $i, X13 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.37/0.62           = (k2_xboole_0 @ X12 @ X13))),
% 0.37/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.62  thf('28', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.37/0.62           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['26', '27'])).
% 0.37/0.62  thf('29', plain,
% 0.37/0.62      (![X12 : $i, X13 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.37/0.62           = (k2_xboole_0 @ X12 @ X13))),
% 0.37/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.62  thf('30', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ X0 @ X1)
% 0.37/0.62           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.62  thf('31', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ X0 @ X1)
% 0.37/0.62           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.62  thf('32', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1)
% 0.37/0.62           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['30', '31'])).
% 0.37/0.62  thf('33', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.62  thf('34', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ X0 @ X1)
% 0.37/0.62           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.62  thf('35', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ X1 @ X0)
% 0.37/0.62           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.62      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.37/0.62  thf(t4_xboole_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.62       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.62  thf('36', plain,
% 0.37/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ (k2_xboole_0 @ X22 @ X23) @ X24)
% 0.37/0.62           = (k2_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.37/0.62  thf('37', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.62  thf('38', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ X0 @ X1)
% 0.37/0.62           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.62  thf('39', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ X1 @ X0)
% 0.37/0.62           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['37', '38'])).
% 0.37/0.62  thf('40', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ X1 @ X0)
% 0.37/0.62           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.62      inference('demod', [status(thm)], ['35', '36', '39'])).
% 0.37/0.62  thf('41', plain,
% 0.37/0.62      (![X15 : $i, X16 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.37/0.62           = (k4_xboole_0 @ X15 @ X16))),
% 0.37/0.62      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.37/0.62  thf('42', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.37/0.62           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['40', '41'])).
% 0.37/0.62  thf(t3_boole, axiom,
% 0.37/0.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.62  thf('43', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.37/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.62  thf(t48_xboole_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.62  thf('44', plain,
% 0.37/0.62      (![X20 : $i, X21 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.37/0.62           = (k3_xboole_0 @ X20 @ X21))),
% 0.37/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.62  thf('45', plain,
% 0.37/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['43', '44'])).
% 0.37/0.62  thf(t2_boole, axiom,
% 0.37/0.62    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.62  thf('46', plain,
% 0.37/0.62      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.62      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.62  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.62      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.62  thf('48', plain,
% 0.37/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.37/0.62           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.37/0.62  thf('49', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['42', '47', '48'])).
% 0.37/0.62  thf('50', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 0.37/0.62      inference('demod', [status(thm)], ['25', '49'])).
% 0.37/0.62  thf('51', plain,
% 0.37/0.62      (![X12 : $i, X13 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.37/0.62           = (k2_xboole_0 @ X12 @ X13))),
% 0.37/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.62  thf('52', plain,
% 0.37/0.62      (![X15 : $i, X16 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.37/0.62           = (k4_xboole_0 @ X15 @ X16))),
% 0.37/0.62      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.37/0.62  thf('53', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.37/0.62           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['51', '52'])).
% 0.37/0.62  thf('54', plain,
% 0.37/0.62      (((k4_xboole_0 @ (k2_xboole_0 @ sk_D @ sk_A) @ k1_xboole_0)
% 0.37/0.62         = (k4_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_A @ sk_D)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['50', '53'])).
% 0.37/0.62  thf('55', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.62  thf('56', plain,
% 0.37/0.62      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.62  thf('57', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ X0 @ X1)
% 0.37/0.62           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.62  thf('58', plain,
% 0.37/0.62      (((k2_xboole_0 @ sk_D @ sk_C_1)
% 0.37/0.62         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['56', '57'])).
% 0.37/0.62  thf('59', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.62  thf('60', plain,
% 0.37/0.62      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.62  thf('61', plain,
% 0.37/0.62      (((k2_xboole_0 @ sk_B_1 @ sk_A)
% 0.37/0.62         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.37/0.62  thf('62', plain,
% 0.37/0.62      (![X15 : $i, X16 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.37/0.62           = (k4_xboole_0 @ X15 @ X16))),
% 0.37/0.62      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.37/0.62  thf('63', plain,
% 0.37/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.37/0.62           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.37/0.62  thf('64', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ 
% 0.37/0.62           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1) @ 
% 0.37/0.62           X0) = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['62', '63'])).
% 0.37/0.62  thf('65', plain,
% 0.37/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.37/0.62           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.37/0.62  thf('66', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ 
% 0.37/0.62           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1) @ 
% 0.37/0.62           X0) = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['64', '65'])).
% 0.37/0.62  thf('67', plain,
% 0.37/0.62      (((k4_xboole_0 @ 
% 0.37/0.62         (k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_B_1) @ sk_A)
% 0.37/0.62         = (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B_1) @ sk_A))),
% 0.37/0.62      inference('sup+', [status(thm)], ['61', '66'])).
% 0.37/0.62  thf('68', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.62  thf('69', plain,
% 0.37/0.62      (![X15 : $i, X16 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.37/0.62           = (k4_xboole_0 @ X15 @ X16))),
% 0.37/0.62      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.37/0.62  thf('70', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.37/0.62           = (k4_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('sup+', [status(thm)], ['68', '69'])).
% 0.37/0.62  thf('71', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['42', '47', '48'])).
% 0.37/0.62  thf('72', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('73', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.62  thf('74', plain, (((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['72', '73'])).
% 0.37/0.62  thf('75', plain,
% 0.37/0.62      (![X25 : $i, X26 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ (k4_xboole_0 @ X25 @ X26))
% 0.37/0.62           = (X25))),
% 0.37/0.62      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.37/0.62  thf('76', plain,
% 0.37/0.62      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B_1)) = (sk_D))),
% 0.37/0.62      inference('sup+', [status(thm)], ['74', '75'])).
% 0.37/0.62  thf('77', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf('78', plain, (((k4_xboole_0 @ sk_D @ sk_B_1) = (sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['76', '77'])).
% 0.37/0.62  thf('79', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['67', '70', '71', '78'])).
% 0.37/0.62  thf('80', plain,
% 0.37/0.62      (![X12 : $i, X13 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.37/0.62           = (k2_xboole_0 @ X12 @ X13))),
% 0.37/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.62  thf('81', plain,
% 0.37/0.62      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.37/0.62      inference('sup+', [status(thm)], ['79', '80'])).
% 0.37/0.62  thf('82', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.62  thf('83', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf('84', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.37/0.62  thf('85', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.37/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.62  thf('86', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 0.37/0.62      inference('demod', [status(thm)], ['25', '49'])).
% 0.37/0.62  thf('87', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.37/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.62  thf('88', plain, (((sk_A) = (sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['54', '55', '84', '85', '86', '87'])).
% 0.37/0.62  thf('89', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.62      inference('demod', [status(thm)], ['6', '88'])).
% 0.37/0.62  thf('90', plain,
% 0.37/0.62      (![X25 : $i, X26 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ (k4_xboole_0 @ X25 @ X26))
% 0.37/0.62           = (X25))),
% 0.37/0.62      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.37/0.62  thf('91', plain,
% 0.37/0.62      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_A)) = (sk_B_1))),
% 0.37/0.62      inference('sup+', [status(thm)], ['89', '90'])).
% 0.37/0.62  thf('92', plain,
% 0.37/0.62      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.62  thf('93', plain,
% 0.37/0.62      (![X15 : $i, X16 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.37/0.62           = (k4_xboole_0 @ X15 @ X16))),
% 0.37/0.62      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.37/0.62  thf('94', plain,
% 0.37/0.62      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D)
% 0.37/0.62         = (k4_xboole_0 @ sk_C_1 @ sk_D))),
% 0.37/0.62      inference('sup+', [status(thm)], ['92', '93'])).
% 0.37/0.62  thf('95', plain, (((sk_A) = (sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['54', '55', '84', '85', '86', '87'])).
% 0.37/0.62  thf('96', plain,
% 0.37/0.62      (![X15 : $i, X16 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.37/0.62           = (k4_xboole_0 @ X15 @ X16))),
% 0.37/0.62      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.37/0.62  thf('97', plain, (((sk_A) = (sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['54', '55', '84', '85', '86', '87'])).
% 0.37/0.62  thf('98', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('99', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.62  thf('100', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['98', '99'])).
% 0.37/0.62  thf('101', plain,
% 0.37/0.62      (![X25 : $i, X26 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ (k4_xboole_0 @ X25 @ X26))
% 0.37/0.62           = (X25))),
% 0.37/0.62      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.37/0.62  thf('102', plain,
% 0.37/0.62      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_A)) = (sk_C_1))),
% 0.37/0.62      inference('sup+', [status(thm)], ['100', '101'])).
% 0.37/0.62  thf('103', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf('104', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.37/0.62      inference('demod', [status(thm)], ['102', '103'])).
% 0.37/0.62  thf('105', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.37/0.62      inference('demod', [status(thm)], ['94', '95', '96', '97', '104'])).
% 0.37/0.62  thf('106', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf('107', plain, (((sk_C_1) = (sk_B_1))),
% 0.37/0.62      inference('demod', [status(thm)], ['91', '105', '106'])).
% 0.37/0.62  thf('108', plain, (((sk_C_1) != (sk_B_1))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('109', plain, ($false),
% 0.37/0.62      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
