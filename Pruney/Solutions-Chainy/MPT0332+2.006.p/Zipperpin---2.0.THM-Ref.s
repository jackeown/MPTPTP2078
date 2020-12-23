%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pUMvctNxXi

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:07 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 542 expanded)
%              Number of leaves         :   23 ( 193 expanded)
%              Depth                    :   21
%              Number of atoms          :  758 (4181 expanded)
%              Number of equality atoms :   84 ( 526 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t145_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t145_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ X45 @ X46 )
      | ( r2_hidden @ X47 @ X46 )
      | ( X46
        = ( k4_xboole_0 @ X46 @ ( k2_tarski @ X45 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('2',plain,(
    sk_C
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('22',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','26'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','26'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','25'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','25'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','54'])).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','26'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','54'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','69'])).

thf('71',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','70'])).

thf('72',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pUMvctNxXi
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.80/1.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.80/1.02  % Solved by: fo/fo7.sh
% 0.80/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.02  % done 533 iterations in 0.525s
% 0.80/1.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.80/1.02  % SZS output start Refutation
% 0.80/1.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.80/1.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.80/1.02  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.80/1.02  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.80/1.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.80/1.02  thf(sk_C_type, type, sk_C: $i).
% 0.80/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.80/1.02  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.80/1.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/1.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.80/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.02  thf(t145_zfmisc_1, conjecture,
% 0.80/1.02    (![A:$i,B:$i,C:$i]:
% 0.80/1.02     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.80/1.02          ( ( C ) !=
% 0.80/1.02            ( k4_xboole_0 @
% 0.80/1.02              ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 0.80/1.02              ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.80/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.02    (~( ![A:$i,B:$i,C:$i]:
% 0.80/1.02        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.80/1.02             ( ( C ) !=
% 0.80/1.02               ( k4_xboole_0 @
% 0.80/1.02                 ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 0.80/1.02                 ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.80/1.02    inference('cnf.neg', [status(esa)], [t145_zfmisc_1])).
% 0.80/1.02  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(t144_zfmisc_1, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i]:
% 0.80/1.02     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.80/1.02          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.80/1.02  thf('1', plain,
% 0.80/1.02      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.80/1.02         ((r2_hidden @ X45 @ X46)
% 0.80/1.02          | (r2_hidden @ X47 @ X46)
% 0.80/1.02          | ((X46) = (k4_xboole_0 @ X46 @ (k2_tarski @ X45 @ X47))))),
% 0.80/1.02      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.80/1.02  thf('2', plain,
% 0.80/1.02      (((sk_C)
% 0.80/1.02         != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.80/1.02             (k2_tarski @ sk_A @ sk_B)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(commutativity_k2_tarski, axiom,
% 0.80/1.02    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.80/1.02  thf('3', plain,
% 0.80/1.02      (![X14 : $i, X15 : $i]:
% 0.80/1.02         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.80/1.02      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.80/1.02  thf(l51_zfmisc_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.80/1.02  thf('4', plain,
% 0.80/1.02      (![X43 : $i, X44 : $i]:
% 0.80/1.02         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.80/1.02      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.80/1.02  thf('5', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('sup+', [status(thm)], ['3', '4'])).
% 0.80/1.02  thf('6', plain,
% 0.80/1.02      (![X43 : $i, X44 : $i]:
% 0.80/1.02         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.80/1.02      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.80/1.02  thf('7', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('sup+', [status(thm)], ['5', '6'])).
% 0.80/1.02  thf('8', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('sup+', [status(thm)], ['5', '6'])).
% 0.80/1.02  thf(t6_xboole_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.80/1.02  thf('9', plain,
% 0.80/1.02      (![X6 : $i, X7 : $i]:
% 0.80/1.02         ((k2_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7))
% 0.80/1.02           = (k2_xboole_0 @ X6 @ X7))),
% 0.80/1.02      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.80/1.02  thf(t95_xboole_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( k3_xboole_0 @ A @ B ) =
% 0.80/1.02       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.80/1.02  thf('10', plain,
% 0.80/1.02      (![X12 : $i, X13 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X12 @ X13)
% 0.80/1.02           = (k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ 
% 0.80/1.02              (k2_xboole_0 @ X12 @ X13)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.80/1.02  thf(commutativity_k5_xboole_0, axiom,
% 0.80/1.02    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.80/1.02  thf('11', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.80/1.02  thf('12', plain,
% 0.80/1.02      (![X12 : $i, X13 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X12 @ X13)
% 0.80/1.02           = (k5_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ 
% 0.80/1.02              (k5_xboole_0 @ X12 @ X13)))),
% 0.80/1.02      inference('demod', [status(thm)], ['10', '11'])).
% 0.80/1.02  thf('13', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.80/1.02           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.80/1.02              (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.80/1.02      inference('sup+', [status(thm)], ['9', '12'])).
% 0.80/1.02  thf('14', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.80/1.02  thf(t92_xboole_1, axiom,
% 0.80/1.02    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.80/1.02  thf('15', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.80/1.02      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.80/1.02  thf(t91_xboole_1, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i]:
% 0.80/1.02     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.80/1.02       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.80/1.02  thf('16', plain,
% 0.80/1.02      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.80/1.02         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.80/1.02           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.80/1.02  thf('17', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.80/1.02           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['15', '16'])).
% 0.80/1.02  thf(idempotence_k2_xboole_0, axiom,
% 0.80/1.02    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.80/1.02  thf('18', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.80/1.02      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.80/1.02  thf('19', plain,
% 0.80/1.02      (![X12 : $i, X13 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X12 @ X13)
% 0.80/1.02           = (k5_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ 
% 0.80/1.02              (k5_xboole_0 @ X12 @ X13)))),
% 0.80/1.02      inference('demod', [status(thm)], ['10', '11'])).
% 0.80/1.02  thf('20', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X0 @ X0)
% 0.80/1.02           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['18', '19'])).
% 0.80/1.02  thf(idempotence_k3_xboole_0, axiom,
% 0.80/1.02    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.80/1.02  thf('21', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.80/1.02      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.80/1.02  thf('22', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.80/1.02      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.80/1.02  thf('23', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.80/1.02      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.80/1.02  thf('24', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.80/1.02  thf('25', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.80/1.02      inference('sup+', [status(thm)], ['23', '24'])).
% 0.80/1.02  thf('26', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('demod', [status(thm)], ['17', '25'])).
% 0.80/1.02  thf('27', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['14', '26'])).
% 0.80/1.02  thf('28', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.80/1.02      inference('demod', [status(thm)], ['13', '27'])).
% 0.80/1.02  thf('29', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.80/1.02      inference('sup+', [status(thm)], ['8', '28'])).
% 0.80/1.02  thf('30', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.80/1.02  thf('31', plain,
% 0.80/1.02      (![X12 : $i, X13 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X12 @ X13)
% 0.80/1.02           = (k5_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ 
% 0.80/1.02              (k5_xboole_0 @ X12 @ X13)))),
% 0.80/1.02      inference('demod', [status(thm)], ['10', '11'])).
% 0.80/1.02  thf('32', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X0 @ X1)
% 0.80/1.02           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['30', '31'])).
% 0.80/1.02  thf('33', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('sup+', [status(thm)], ['5', '6'])).
% 0.80/1.02  thf('34', plain,
% 0.80/1.02      (![X12 : $i, X13 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X12 @ X13)
% 0.80/1.02           = (k5_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ 
% 0.80/1.02              (k5_xboole_0 @ X12 @ X13)))),
% 0.80/1.02      inference('demod', [status(thm)], ['10', '11'])).
% 0.80/1.02  thf('35', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X0 @ X1)
% 0.80/1.02           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['33', '34'])).
% 0.80/1.02  thf('36', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 0.80/1.02      inference('sup+', [status(thm)], ['32', '35'])).
% 0.80/1.02  thf(t100_xboole_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.80/1.02  thf('37', plain,
% 0.80/1.02      (![X4 : $i, X5 : $i]:
% 0.80/1.02         ((k4_xboole_0 @ X4 @ X5)
% 0.80/1.02           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.80/1.02  thf('38', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k4_xboole_0 @ X0 @ X1)
% 0.80/1.02           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['36', '37'])).
% 0.80/1.02  thf('39', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['14', '26'])).
% 0.80/1.02  thf('40', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((X1)
% 0.80/1.02           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['38', '39'])).
% 0.80/1.02  thf('41', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k2_xboole_0 @ X1 @ X0)
% 0.80/1.02           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['29', '40'])).
% 0.80/1.02  thf('42', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('sup+', [status(thm)], ['5', '6'])).
% 0.80/1.02  thf('43', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X0 @ X1)
% 0.80/1.02           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['30', '31'])).
% 0.80/1.02  thf('44', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['14', '26'])).
% 0.80/1.02  thf('45', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k2_xboole_0 @ X1 @ X0)
% 0.80/1.02           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['43', '44'])).
% 0.80/1.02  thf('46', plain,
% 0.80/1.02      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.80/1.02         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.80/1.02           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.80/1.02  thf('47', plain,
% 0.80/1.02      (![X4 : $i, X5 : $i]:
% 0.80/1.02         ((k4_xboole_0 @ X4 @ X5)
% 0.80/1.02           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.80/1.02  thf('48', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k2_xboole_0 @ X1 @ X0)
% 0.80/1.02           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.80/1.02  thf('49', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('demod', [status(thm)], ['17', '25'])).
% 0.80/1.02  thf('50', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k4_xboole_0 @ X1 @ X0)
% 0.80/1.02           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['48', '49'])).
% 0.80/1.02  thf('51', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k4_xboole_0 @ X0 @ X1)
% 0.80/1.02           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['42', '50'])).
% 0.80/1.02  thf('52', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('demod', [status(thm)], ['17', '25'])).
% 0.80/1.02  thf('53', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k2_xboole_0 @ X0 @ X1)
% 0.80/1.02           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['51', '52'])).
% 0.80/1.02  thf('54', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k2_xboole_0 @ X1 @ X0)
% 0.80/1.02           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('demod', [status(thm)], ['41', '53'])).
% 0.80/1.02  thf('55', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k2_xboole_0 @ X0 @ X1)
% 0.80/1.02           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['7', '54'])).
% 0.80/1.02  thf('56', plain,
% 0.80/1.02      (![X6 : $i, X7 : $i]:
% 0.80/1.02         ((k2_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7))
% 0.80/1.02           = (k2_xboole_0 @ X6 @ X7))),
% 0.80/1.02      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.80/1.02  thf('57', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X0 @ X1)
% 0.80/1.02           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['33', '34'])).
% 0.80/1.02  thf('58', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.80/1.02           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.80/1.02              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['56', '57'])).
% 0.80/1.02  thf('59', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.80/1.02  thf('60', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['14', '26'])).
% 0.80/1.02  thf('61', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.80/1.02      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.80/1.02  thf('62', plain,
% 0.80/1.02      (![X4 : $i, X5 : $i]:
% 0.80/1.02         ((k4_xboole_0 @ X4 @ X5)
% 0.80/1.02           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.80/1.02  thf('63', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.80/1.02           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.80/1.02      inference('sup+', [status(thm)], ['61', '62'])).
% 0.80/1.02  thf('64', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.80/1.02  thf('65', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.80/1.02           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.80/1.02      inference('demod', [status(thm)], ['63', '64'])).
% 0.80/1.02  thf('66', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ X0)
% 0.80/1.02           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['55', '65'])).
% 0.80/1.02  thf('67', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k2_xboole_0 @ X0 @ X1)
% 0.80/1.02           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['7', '54'])).
% 0.80/1.02  thf('68', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k4_xboole_0 @ X1 @ X0)
% 0.80/1.02           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['48', '49'])).
% 0.80/1.02  thf('69', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.80/1.02           = (k4_xboole_0 @ X1 @ X0))),
% 0.80/1.02      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.80/1.02  thf('70', plain,
% 0.80/1.02      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.80/1.02      inference('demod', [status(thm)], ['2', '69'])).
% 0.80/1.02  thf('71', plain,
% 0.80/1.02      ((((sk_C) != (sk_C))
% 0.80/1.02        | (r2_hidden @ sk_B @ sk_C)
% 0.80/1.02        | (r2_hidden @ sk_A @ sk_C))),
% 0.80/1.02      inference('sup-', [status(thm)], ['1', '70'])).
% 0.80/1.02  thf('72', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 0.80/1.02      inference('simplify', [status(thm)], ['71'])).
% 0.80/1.02  thf('73', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('74', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.80/1.02      inference('clc', [status(thm)], ['72', '73'])).
% 0.80/1.02  thf('75', plain, ($false), inference('demod', [status(thm)], ['0', '74'])).
% 0.80/1.02  
% 0.80/1.02  % SZS output end Refutation
% 0.80/1.02  
% 0.80/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
