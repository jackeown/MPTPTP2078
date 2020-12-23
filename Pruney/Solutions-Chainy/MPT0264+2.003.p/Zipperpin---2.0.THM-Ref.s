%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Yd7WZ9z5mV

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:38 EST 2020

% Result     : Theorem 4.47s
% Output     : Refutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 189 expanded)
%              Number of leaves         :   31 (  71 expanded)
%              Depth                    :   18
%              Number of atoms          :  872 (1585 expanded)
%              Number of equality atoms :   73 ( 154 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('2',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X12 ) )
      | ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_B @ X1 )
      | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('22',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('24',plain,(
    ! [X68: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X68 ) )
      = X68 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X0
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','28'])).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X0
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','28'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('35',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X12 ) )
      | ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('39',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_B @ ( k5_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k5_xboole_0 @ X0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_B @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['33','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ sk_C_1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ sk_C_1 @ X0 ) ) @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ sk_B @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_C_1 ) @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) @ ( k2_xboole_0 @ X0 @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) )
    | ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','57'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('60',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) )
    | ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','64'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_enumset1 @ X39 @ X39 @ X40 )
      = ( k2_tarski @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X26 @ X30 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('68',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) )
      | ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X23 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('71',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X23 @ X24 @ X21 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['65','72'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('74',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X36 @ X35 )
      | ( X36 = X33 )
      | ( X35
       != ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('75',plain,(
    ! [X33: $i,X36: $i] :
      ( ( X36 = X33 )
      | ~ ( r2_hidden @ X36 @ ( k1_tarski @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Yd7WZ9z5mV
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.47/4.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.47/4.70  % Solved by: fo/fo7.sh
% 4.47/4.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.47/4.70  % done 3023 iterations in 4.254s
% 4.47/4.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.47/4.70  % SZS output start Refutation
% 4.47/4.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.47/4.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.47/4.70  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 4.47/4.70  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.47/4.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.47/4.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.47/4.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.47/4.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.47/4.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 4.47/4.70  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.47/4.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.47/4.70  thf(sk_A_type, type, sk_A: $i).
% 4.47/4.70  thf(sk_B_type, type, sk_B: $i).
% 4.47/4.70  thf(t59_zfmisc_1, conjecture,
% 4.47/4.70    (![A:$i,B:$i,C:$i]:
% 4.47/4.70     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 4.47/4.70          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 4.47/4.70  thf(zf_stmt_0, negated_conjecture,
% 4.47/4.70    (~( ![A:$i,B:$i,C:$i]:
% 4.47/4.70        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 4.47/4.70             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 4.47/4.70    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 4.47/4.70  thf('0', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 4.47/4.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.70  thf(d3_xboole_0, axiom,
% 4.47/4.70    (![A:$i,B:$i,C:$i]:
% 4.47/4.70     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 4.47/4.70       ( ![D:$i]:
% 4.47/4.70         ( ( r2_hidden @ D @ C ) <=>
% 4.47/4.70           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 4.47/4.70  thf('1', plain,
% 4.47/4.70      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.47/4.70         (~ (r2_hidden @ X2 @ X5)
% 4.47/4.70          | (r2_hidden @ X2 @ X4)
% 4.47/4.70          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 4.47/4.70      inference('cnf', [status(esa)], [d3_xboole_0])).
% 4.47/4.70  thf('2', plain,
% 4.47/4.70      (![X2 : $i, X3 : $i, X5 : $i]:
% 4.47/4.70         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 4.47/4.70      inference('simplify', [status(thm)], ['1'])).
% 4.47/4.70  thf('3', plain,
% 4.47/4.70      (![X0 : $i]: (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0))),
% 4.47/4.70      inference('sup-', [status(thm)], ['0', '2'])).
% 4.47/4.70  thf(t1_xboole_0, axiom,
% 4.47/4.70    (![A:$i,B:$i,C:$i]:
% 4.47/4.70     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 4.47/4.70       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 4.47/4.70  thf('4', plain,
% 4.47/4.70      (![X9 : $i, X10 : $i, X12 : $i]:
% 4.47/4.70         ((r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X12))
% 4.47/4.70          | (r2_hidden @ X9 @ X10)
% 4.47/4.70          | ~ (r2_hidden @ X9 @ X12))),
% 4.47/4.70      inference('cnf', [status(esa)], [t1_xboole_0])).
% 4.47/4.70  thf('5', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]:
% 4.47/4.70         ((r2_hidden @ sk_B @ X1)
% 4.47/4.70          | (r2_hidden @ sk_B @ 
% 4.47/4.70             (k5_xboole_0 @ X1 @ (k2_xboole_0 @ sk_C_1 @ X0))))),
% 4.47/4.70      inference('sup-', [status(thm)], ['3', '4'])).
% 4.47/4.70  thf('6', plain,
% 4.47/4.70      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_tarski @ sk_A))),
% 4.47/4.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.70  thf(t95_xboole_1, axiom,
% 4.47/4.70    (![A:$i,B:$i]:
% 4.47/4.70     ( ( k3_xboole_0 @ A @ B ) =
% 4.47/4.70       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 4.47/4.70  thf('7', plain,
% 4.47/4.70      (![X17 : $i, X18 : $i]:
% 4.47/4.70         ((k3_xboole_0 @ X17 @ X18)
% 4.47/4.70           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 4.47/4.70              (k2_xboole_0 @ X17 @ X18)))),
% 4.47/4.70      inference('cnf', [status(esa)], [t95_xboole_1])).
% 4.47/4.70  thf(commutativity_k5_xboole_0, axiom,
% 4.47/4.70    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 4.47/4.70  thf('8', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 4.47/4.70      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 4.47/4.70  thf(t91_xboole_1, axiom,
% 4.47/4.70    (![A:$i,B:$i,C:$i]:
% 4.47/4.70     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 4.47/4.70       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 4.47/4.70  thf('9', plain,
% 4.47/4.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.47/4.70         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 4.47/4.70           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 4.47/4.70      inference('cnf', [status(esa)], [t91_xboole_1])).
% 4.47/4.70  thf('10', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.47/4.70         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 4.47/4.70           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 4.47/4.70      inference('sup+', [status(thm)], ['8', '9'])).
% 4.47/4.70  thf('11', plain,
% 4.47/4.70      (![X17 : $i, X18 : $i]:
% 4.47/4.70         ((k3_xboole_0 @ X17 @ X18)
% 4.47/4.70           = (k5_xboole_0 @ X18 @ 
% 4.47/4.70              (k5_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18))))),
% 4.47/4.70      inference('demod', [status(thm)], ['7', '10'])).
% 4.47/4.70  thf('12', plain,
% 4.47/4.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.47/4.70         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 4.47/4.70           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 4.47/4.70      inference('cnf', [status(esa)], [t91_xboole_1])).
% 4.47/4.70  thf(t92_xboole_1, axiom,
% 4.47/4.70    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 4.47/4.70  thf('13', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 4.47/4.70      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.47/4.70  thf('14', plain,
% 4.47/4.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.47/4.70         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 4.47/4.70           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 4.47/4.70      inference('cnf', [status(esa)], [t91_xboole_1])).
% 4.47/4.70  thf('15', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]:
% 4.47/4.70         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 4.47/4.70           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.47/4.70      inference('sup+', [status(thm)], ['13', '14'])).
% 4.47/4.70  thf('16', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.47/4.70         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 4.47/4.70           = (k5_xboole_0 @ X2 @ 
% 4.47/4.70              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0))))),
% 4.47/4.70      inference('sup+', [status(thm)], ['12', '15'])).
% 4.47/4.70  thf('17', plain,
% 4.47/4.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.47/4.70         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 4.47/4.70           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 4.47/4.70      inference('cnf', [status(esa)], [t91_xboole_1])).
% 4.47/4.70  thf('18', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.47/4.70         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 4.47/4.70           = (k5_xboole_0 @ X2 @ 
% 4.47/4.70              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 4.47/4.70      inference('demod', [status(thm)], ['16', '17'])).
% 4.47/4.70  thf('19', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]:
% 4.47/4.70         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 4.47/4.70           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.47/4.70      inference('sup+', [status(thm)], ['13', '14'])).
% 4.47/4.70  thf('20', plain,
% 4.47/4.70      (![X17 : $i, X18 : $i]:
% 4.47/4.70         ((k3_xboole_0 @ X17 @ X18)
% 4.47/4.70           = (k5_xboole_0 @ X18 @ 
% 4.47/4.70              (k5_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18))))),
% 4.47/4.70      inference('demod', [status(thm)], ['7', '10'])).
% 4.47/4.70  thf('21', plain,
% 4.47/4.70      (![X0 : $i]:
% 4.47/4.70         ((k3_xboole_0 @ X0 @ X0)
% 4.47/4.70           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 4.47/4.70      inference('sup+', [status(thm)], ['19', '20'])).
% 4.47/4.70  thf(idempotence_k3_xboole_0, axiom,
% 4.47/4.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 4.47/4.70  thf('22', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 4.47/4.70      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 4.47/4.70  thf(t69_enumset1, axiom,
% 4.47/4.70    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.47/4.70  thf('23', plain,
% 4.47/4.70      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 4.47/4.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.47/4.70  thf(t31_zfmisc_1, axiom,
% 4.47/4.70    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 4.47/4.70  thf('24', plain, (![X68 : $i]: ((k3_tarski @ (k1_tarski @ X68)) = (X68))),
% 4.47/4.70      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 4.47/4.70  thf('25', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 4.47/4.70      inference('sup+', [status(thm)], ['23', '24'])).
% 4.47/4.70  thf(l51_zfmisc_1, axiom,
% 4.47/4.70    (![A:$i,B:$i]:
% 4.47/4.70     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.47/4.70  thf('26', plain,
% 4.47/4.70      (![X66 : $i, X67 : $i]:
% 4.47/4.70         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 4.47/4.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.47/4.70  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 4.47/4.70      inference('demod', [status(thm)], ['25', '26'])).
% 4.47/4.70  thf('28', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 4.47/4.70      inference('demod', [status(thm)], ['21', '22', '27'])).
% 4.47/4.70  thf('29', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.47/4.70         ((X0)
% 4.47/4.70           = (k5_xboole_0 @ X2 @ 
% 4.47/4.70              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 4.47/4.70      inference('demod', [status(thm)], ['18', '28'])).
% 4.47/4.70  thf('30', plain,
% 4.47/4.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.47/4.70         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 4.47/4.70           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 4.47/4.70      inference('cnf', [status(esa)], [t91_xboole_1])).
% 4.47/4.70  thf('31', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 4.47/4.70      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 4.47/4.70  thf('32', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.47/4.70         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 4.47/4.70           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.47/4.70      inference('sup+', [status(thm)], ['30', '31'])).
% 4.47/4.70  thf('33', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.47/4.70         ((X0)
% 4.47/4.70           = (k5_xboole_0 @ X2 @ 
% 4.47/4.70              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 4.47/4.70      inference('demod', [status(thm)], ['18', '28'])).
% 4.47/4.70  thf('34', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 4.47/4.70      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 4.47/4.70  thf('35', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 4.47/4.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.70  thf('36', plain,
% 4.47/4.70      (![X9 : $i, X10 : $i, X12 : $i]:
% 4.47/4.70         ((r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X12))
% 4.47/4.70          | (r2_hidden @ X9 @ X10)
% 4.47/4.70          | ~ (r2_hidden @ X9 @ X12))),
% 4.47/4.70      inference('cnf', [status(esa)], [t1_xboole_0])).
% 4.47/4.70  thf('37', plain,
% 4.47/4.70      (![X0 : $i]:
% 4.47/4.70         ((r2_hidden @ sk_B @ X0)
% 4.47/4.70          | (r2_hidden @ sk_B @ (k5_xboole_0 @ X0 @ sk_C_1)))),
% 4.47/4.70      inference('sup-', [status(thm)], ['35', '36'])).
% 4.47/4.70  thf('38', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]:
% 4.47/4.70         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 4.47/4.70           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.47/4.70      inference('sup+', [status(thm)], ['13', '14'])).
% 4.47/4.70  thf('39', plain,
% 4.47/4.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.47/4.70         (~ (r2_hidden @ X9 @ X10)
% 4.47/4.70          | ~ (r2_hidden @ X9 @ X11)
% 4.47/4.70          | ~ (r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 4.47/4.70      inference('cnf', [status(esa)], [t1_xboole_0])).
% 4.47/4.70  thf('40', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.47/4.70         (~ (r2_hidden @ X2 @ (k5_xboole_0 @ k1_xboole_0 @ X0))
% 4.47/4.70          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 4.47/4.70          | ~ (r2_hidden @ X2 @ X1))),
% 4.47/4.70      inference('sup-', [status(thm)], ['38', '39'])).
% 4.47/4.70  thf('41', plain,
% 4.47/4.70      (![X0 : $i]:
% 4.47/4.70         ((r2_hidden @ sk_B @ k1_xboole_0)
% 4.47/4.70          | ~ (r2_hidden @ sk_B @ X0)
% 4.47/4.70          | ~ (r2_hidden @ sk_B @ (k5_xboole_0 @ X0 @ sk_C_1)))),
% 4.47/4.70      inference('sup-', [status(thm)], ['37', '40'])).
% 4.47/4.70  thf('42', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 4.47/4.70      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.47/4.70  thf('43', plain,
% 4.47/4.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.47/4.70         (~ (r2_hidden @ X9 @ X10)
% 4.47/4.70          | ~ (r2_hidden @ X9 @ X11)
% 4.47/4.70          | ~ (r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 4.47/4.70      inference('cnf', [status(esa)], [t1_xboole_0])).
% 4.47/4.70  thf('44', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]:
% 4.47/4.70         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 4.47/4.70          | ~ (r2_hidden @ X1 @ X0)
% 4.47/4.70          | ~ (r2_hidden @ X1 @ X0))),
% 4.47/4.70      inference('sup-', [status(thm)], ['42', '43'])).
% 4.47/4.70  thf('45', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]:
% 4.47/4.70         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 4.47/4.70      inference('simplify', [status(thm)], ['44'])).
% 4.47/4.70  thf('46', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 4.47/4.70      inference('condensation', [status(thm)], ['45'])).
% 4.47/4.70  thf('47', plain,
% 4.47/4.70      (![X0 : $i]:
% 4.47/4.70         (~ (r2_hidden @ sk_B @ (k5_xboole_0 @ X0 @ sk_C_1))
% 4.47/4.70          | ~ (r2_hidden @ sk_B @ X0))),
% 4.47/4.70      inference('clc', [status(thm)], ['41', '46'])).
% 4.47/4.70  thf('48', plain,
% 4.47/4.70      (![X0 : $i]:
% 4.47/4.70         (~ (r2_hidden @ sk_B @ (k5_xboole_0 @ sk_C_1 @ X0))
% 4.47/4.70          | ~ (r2_hidden @ sk_B @ X0))),
% 4.47/4.70      inference('sup-', [status(thm)], ['34', '47'])).
% 4.47/4.70  thf('49', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]:
% 4.47/4.70         (~ (r2_hidden @ sk_B @ X0)
% 4.47/4.70          | ~ (r2_hidden @ sk_B @ 
% 4.47/4.70               (k5_xboole_0 @ X1 @ 
% 4.47/4.70                (k5_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ X1 @ X0)))))),
% 4.47/4.70      inference('sup-', [status(thm)], ['33', '48'])).
% 4.47/4.70  thf('50', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]:
% 4.47/4.70         (~ (r2_hidden @ sk_B @ 
% 4.47/4.70             (k5_xboole_0 @ X0 @ 
% 4.47/4.70              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ sk_C_1 @ X0))))
% 4.47/4.70          | ~ (r2_hidden @ sk_B @ X1))),
% 4.47/4.70      inference('sup-', [status(thm)], ['32', '49'])).
% 4.47/4.70  thf('51', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]:
% 4.47/4.70         (~ (r2_hidden @ sk_B @ 
% 4.47/4.70             (k5_xboole_0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ sk_C_1 @ X0)) @ 
% 4.47/4.70              X0))
% 4.47/4.70          | ~ (r2_hidden @ sk_B @ X1))),
% 4.47/4.70      inference('sup-', [status(thm)], ['29', '50'])).
% 4.47/4.70  thf('52', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.47/4.70         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 4.47/4.70           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 4.47/4.70      inference('sup+', [status(thm)], ['8', '9'])).
% 4.47/4.70  thf('53', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.47/4.70         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 4.47/4.70           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 4.47/4.70      inference('sup+', [status(thm)], ['8', '9'])).
% 4.47/4.70  thf('54', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]:
% 4.47/4.70         (~ (r2_hidden @ sk_B @ 
% 4.47/4.70             (k5_xboole_0 @ X0 @ 
% 4.47/4.70              (k5_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ X1 @ X0))))
% 4.47/4.70          | ~ (r2_hidden @ sk_B @ X1))),
% 4.47/4.70      inference('demod', [status(thm)], ['51', '52', '53'])).
% 4.47/4.70  thf('55', plain,
% 4.47/4.70      (![X0 : $i]:
% 4.47/4.70         (~ (r2_hidden @ sk_B @ 
% 4.47/4.70             (k5_xboole_0 @ (k2_xboole_0 @ X0 @ sk_C_1) @ 
% 4.47/4.70              (k3_xboole_0 @ X0 @ sk_C_1)))
% 4.47/4.70          | ~ (r2_hidden @ sk_B @ X0))),
% 4.47/4.70      inference('sup-', [status(thm)], ['11', '54'])).
% 4.47/4.70  thf('56', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 4.47/4.70      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 4.47/4.70  thf('57', plain,
% 4.47/4.70      (![X0 : $i]:
% 4.47/4.70         (~ (r2_hidden @ sk_B @ 
% 4.47/4.70             (k5_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_1) @ 
% 4.47/4.70              (k2_xboole_0 @ X0 @ sk_C_1)))
% 4.47/4.70          | ~ (r2_hidden @ sk_B @ X0))),
% 4.47/4.70      inference('demod', [status(thm)], ['55', '56'])).
% 4.47/4.70  thf('58', plain,
% 4.47/4.70      ((~ (r2_hidden @ sk_B @ 
% 4.47/4.70           (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 4.47/4.70            (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))
% 4.47/4.70        | ~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B)))),
% 4.47/4.70      inference('sup-', [status(thm)], ['6', '57'])).
% 4.47/4.70  thf(commutativity_k2_tarski, axiom,
% 4.47/4.70    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 4.47/4.70  thf('59', plain,
% 4.47/4.70      (![X19 : $i, X20 : $i]:
% 4.47/4.70         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 4.47/4.70      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.47/4.70  thf('60', plain,
% 4.47/4.70      (![X66 : $i, X67 : $i]:
% 4.47/4.70         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 4.47/4.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.47/4.70  thf('61', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]:
% 4.47/4.70         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 4.47/4.70      inference('sup+', [status(thm)], ['59', '60'])).
% 4.47/4.70  thf('62', plain,
% 4.47/4.70      (![X66 : $i, X67 : $i]:
% 4.47/4.70         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 4.47/4.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.47/4.70  thf('63', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.47/4.70      inference('sup+', [status(thm)], ['61', '62'])).
% 4.47/4.70  thf('64', plain,
% 4.47/4.70      ((~ (r2_hidden @ sk_B @ 
% 4.47/4.70           (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 4.47/4.70            (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))))
% 4.47/4.70        | ~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B)))),
% 4.47/4.70      inference('demod', [status(thm)], ['58', '63'])).
% 4.47/4.70  thf('65', plain,
% 4.47/4.70      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 4.47/4.70        | ~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B)))),
% 4.47/4.70      inference('sup-', [status(thm)], ['5', '64'])).
% 4.47/4.70  thf(t70_enumset1, axiom,
% 4.47/4.70    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 4.47/4.70  thf('66', plain,
% 4.47/4.70      (![X39 : $i, X40 : $i]:
% 4.47/4.70         ((k1_enumset1 @ X39 @ X39 @ X40) = (k2_tarski @ X39 @ X40))),
% 4.47/4.70      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.47/4.70  thf(d1_enumset1, axiom,
% 4.47/4.70    (![A:$i,B:$i,C:$i,D:$i]:
% 4.47/4.70     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 4.47/4.70       ( ![E:$i]:
% 4.47/4.70         ( ( r2_hidden @ E @ D ) <=>
% 4.47/4.70           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 4.47/4.70  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 4.47/4.70  thf(zf_stmt_2, axiom,
% 4.47/4.70    (![E:$i,C:$i,B:$i,A:$i]:
% 4.47/4.70     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 4.47/4.70       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 4.47/4.70  thf(zf_stmt_3, axiom,
% 4.47/4.70    (![A:$i,B:$i,C:$i,D:$i]:
% 4.47/4.70     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 4.47/4.70       ( ![E:$i]:
% 4.47/4.70         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 4.47/4.70  thf('67', plain,
% 4.47/4.70      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 4.47/4.70         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 4.47/4.70          | (r2_hidden @ X26 @ X30)
% 4.47/4.70          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 4.47/4.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.47/4.70  thf('68', plain,
% 4.47/4.70      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 4.47/4.70         ((r2_hidden @ X26 @ (k1_enumset1 @ X29 @ X28 @ X27))
% 4.47/4.70          | (zip_tseitin_0 @ X26 @ X27 @ X28 @ X29))),
% 4.47/4.70      inference('simplify', [status(thm)], ['67'])).
% 4.47/4.70  thf('69', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.47/4.70         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 4.47/4.70          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 4.47/4.70      inference('sup+', [status(thm)], ['66', '68'])).
% 4.47/4.70  thf('70', plain,
% 4.47/4.70      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 4.47/4.70         (((X22) != (X23)) | ~ (zip_tseitin_0 @ X22 @ X23 @ X24 @ X21))),
% 4.47/4.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.47/4.70  thf('71', plain,
% 4.47/4.70      (![X21 : $i, X23 : $i, X24 : $i]:
% 4.47/4.70         ~ (zip_tseitin_0 @ X23 @ X23 @ X24 @ X21)),
% 4.47/4.70      inference('simplify', [status(thm)], ['70'])).
% 4.47/4.70  thf('72', plain,
% 4.47/4.70      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 4.47/4.70      inference('sup-', [status(thm)], ['69', '71'])).
% 4.47/4.70  thf('73', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 4.47/4.70      inference('demod', [status(thm)], ['65', '72'])).
% 4.47/4.70  thf(d1_tarski, axiom,
% 4.47/4.70    (![A:$i,B:$i]:
% 4.47/4.70     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 4.47/4.70       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 4.47/4.70  thf('74', plain,
% 4.47/4.70      (![X33 : $i, X35 : $i, X36 : $i]:
% 4.47/4.70         (~ (r2_hidden @ X36 @ X35)
% 4.47/4.70          | ((X36) = (X33))
% 4.47/4.70          | ((X35) != (k1_tarski @ X33)))),
% 4.47/4.70      inference('cnf', [status(esa)], [d1_tarski])).
% 4.47/4.70  thf('75', plain,
% 4.47/4.70      (![X33 : $i, X36 : $i]:
% 4.47/4.70         (((X36) = (X33)) | ~ (r2_hidden @ X36 @ (k1_tarski @ X33)))),
% 4.47/4.70      inference('simplify', [status(thm)], ['74'])).
% 4.47/4.70  thf('76', plain, (((sk_B) = (sk_A))),
% 4.47/4.70      inference('sup-', [status(thm)], ['73', '75'])).
% 4.47/4.70  thf('77', plain, (((sk_A) != (sk_B))),
% 4.47/4.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.70  thf('78', plain, ($false),
% 4.47/4.70      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 4.47/4.70  
% 4.47/4.70  % SZS output end Refutation
% 4.47/4.70  
% 4.47/4.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
