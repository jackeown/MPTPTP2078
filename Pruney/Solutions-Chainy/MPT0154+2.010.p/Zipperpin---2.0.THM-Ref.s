%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3kDNtpLaX7

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:22 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  134 (2944 expanded)
%              Number of leaves         :   28 ( 968 expanded)
%              Depth                    :   27
%              Number of atoms          :  992 (23372 expanded)
%              Number of equality atoms :  117 (2753 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t70_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_enumset1 @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t70_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X30 != X32 )
      | ( r2_hidden @ X30 @ X31 )
      | ( X31
       != ( k2_tarski @ X32 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X29: $i,X32: $i] :
      ( r2_hidden @ X32 @ ( k2_tarski @ X32 @ X29 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( X27 = X24 )
      | ( X26
       != ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X24: $i,X27: $i] :
      ( ( X27 = X24 )
      | ~ ( r2_hidden @ X27 @ ( k1_tarski @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('37',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','38'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('41',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','50'])).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','49'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','49'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('74',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('78',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['24','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','80'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['82','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('94',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('97',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['92','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','98'])).

thf('100',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('101',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k1_tarski @ X35 ) @ ( k2_tarski @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','102'])).

thf('104',plain,(
    $false ),
    inference(simplify,[status(thm)],['103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3kDNtpLaX7
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:39:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.76  % Solved by: fo/fo7.sh
% 0.59/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.76  % done 651 iterations in 0.301s
% 0.59/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.76  % SZS output start Refutation
% 0.59/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.76  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.59/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.76  thf(t70_enumset1, conjecture,
% 0.59/0.76    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.59/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.76    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.59/0.76    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.59/0.76  thf('0', plain,
% 0.59/0.76      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(d2_tarski, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i]:
% 0.59/0.76     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.59/0.76       ( ![D:$i]:
% 0.59/0.76         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.59/0.76  thf('1', plain,
% 0.59/0.76      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.59/0.76         (((X30) != (X32))
% 0.59/0.76          | (r2_hidden @ X30 @ X31)
% 0.59/0.76          | ((X31) != (k2_tarski @ X32 @ X29)))),
% 0.59/0.76      inference('cnf', [status(esa)], [d2_tarski])).
% 0.59/0.76  thf('2', plain,
% 0.59/0.76      (![X29 : $i, X32 : $i]: (r2_hidden @ X32 @ (k2_tarski @ X32 @ X29))),
% 0.59/0.76      inference('simplify', [status(thm)], ['1'])).
% 0.59/0.76  thf(d3_tarski, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.76       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.76  thf('3', plain,
% 0.59/0.76      (![X3 : $i, X5 : $i]:
% 0.59/0.76         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.76  thf(d1_tarski, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.59/0.76       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.59/0.76  thf('4', plain,
% 0.59/0.76      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.59/0.76         (~ (r2_hidden @ X27 @ X26)
% 0.59/0.76          | ((X27) = (X24))
% 0.59/0.76          | ((X26) != (k1_tarski @ X24)))),
% 0.59/0.76      inference('cnf', [status(esa)], [d1_tarski])).
% 0.59/0.76  thf('5', plain,
% 0.59/0.76      (![X24 : $i, X27 : $i]:
% 0.59/0.76         (((X27) = (X24)) | ~ (r2_hidden @ X27 @ (k1_tarski @ X24)))),
% 0.59/0.76      inference('simplify', [status(thm)], ['4'])).
% 0.59/0.76  thf('6', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.59/0.76          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['3', '5'])).
% 0.59/0.76  thf('7', plain,
% 0.59/0.76      (![X3 : $i, X5 : $i]:
% 0.59/0.76         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.76  thf('8', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (~ (r2_hidden @ X0 @ X1)
% 0.59/0.76          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.59/0.76          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.59/0.76      inference('sup-', [status(thm)], ['6', '7'])).
% 0.59/0.76  thf('9', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.59/0.76      inference('simplify', [status(thm)], ['8'])).
% 0.59/0.76  thf('10', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.59/0.76      inference('sup-', [status(thm)], ['2', '9'])).
% 0.59/0.76  thf(t28_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.76  thf('11', plain,
% 0.59/0.76      (![X15 : $i, X16 : $i]:
% 0.59/0.76         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.59/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.76  thf('12', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.59/0.76           = (k1_tarski @ X1))),
% 0.59/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.76  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.76  thf('13', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.76  thf(t100_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.76  thf('14', plain,
% 0.59/0.76      (![X10 : $i, X11 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ X10 @ X11)
% 0.59/0.76           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.59/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.76  thf('15', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ X0 @ X1)
% 0.59/0.76           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('16', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))
% 0.59/0.76           = (k5_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0)))),
% 0.59/0.76      inference('sup+', [status(thm)], ['12', '15'])).
% 0.59/0.77  thf(t91_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.77       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.59/0.77           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.77  thf(d10_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.77  thf('19', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.59/0.77      inference('simplify', [status(thm)], ['18'])).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      (![X15 : $i, X16 : $i]:
% 0.59/0.77         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.59/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.77  thf('21', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (![X10 : $i, X11 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X10 @ X11)
% 0.59/0.77           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.77  thf('23', plain,
% 0.59/0.77      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.59/0.77           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.59/0.77      inference('sup+', [status(thm)], ['17', '23'])).
% 0.59/0.77  thf(t48_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.77  thf('25', plain,
% 0.59/0.77      (![X17 : $i, X18 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.77           = (k3_xboole_0 @ X17 @ X18))),
% 0.59/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.77  thf('26', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.77  thf('27', plain,
% 0.59/0.77      (![X17 : $i, X18 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.77           = (k3_xboole_0 @ X17 @ X18))),
% 0.59/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.77  thf(t98_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.59/0.77  thf('28', plain,
% 0.59/0.77      (![X22 : $i, X23 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X22 @ X23)
% 0.59/0.77           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.59/0.77  thf('29', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.59/0.77           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['27', '28'])).
% 0.59/0.77  thf('30', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.59/0.77           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['26', '29'])).
% 0.59/0.77  thf('31', plain,
% 0.59/0.77      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.77  thf('32', plain,
% 0.59/0.77      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.77  thf('33', plain,
% 0.59/0.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.59/0.77           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.77  thf('34', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.59/0.77           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['32', '33'])).
% 0.59/0.77  thf('35', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.59/0.77           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['31', '34'])).
% 0.59/0.77  thf('36', plain,
% 0.59/0.77      (![X22 : $i, X23 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X22 @ X23)
% 0.59/0.77           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.59/0.77  thf(idempotence_k2_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.59/0.77  thf('37', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.59/0.77      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.59/0.77  thf('38', plain,
% 0.59/0.77      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.59/0.77  thf('39', plain,
% 0.59/0.77      (![X0 : $i]: ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['30', '38'])).
% 0.59/0.77  thf(t1_boole, axiom,
% 0.59/0.77    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.77  thf('40', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_boole])).
% 0.59/0.77  thf('41', plain,
% 0.59/0.77      (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['39', '40'])).
% 0.59/0.77  thf('42', plain,
% 0.59/0.77      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.59/0.77  thf('43', plain,
% 0.59/0.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.59/0.77           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.77  thf('44', plain,
% 0.59/0.77      (![X10 : $i, X11 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X10 @ X11)
% 0.59/0.77           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.77  thf('45', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0)
% 0.59/0.77           = (k5_xboole_0 @ X2 @ 
% 0.59/0.77              (k5_xboole_0 @ X1 @ (k3_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0))))),
% 0.59/0.77      inference('sup+', [status(thm)], ['43', '44'])).
% 0.59/0.77  thf('46', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) @ X1)
% 0.59/0.77           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 0.59/0.77              (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.59/0.77      inference('sup+', [status(thm)], ['42', '45'])).
% 0.59/0.77  thf('47', plain,
% 0.59/0.77      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.59/0.77  thf('48', plain,
% 0.59/0.77      (![X10 : $i, X11 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X10 @ X11)
% 0.59/0.77           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.77  thf('49', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X0 @ X1)
% 0.59/0.77           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.59/0.77      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.59/0.77  thf('50', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.59/0.77           = (k5_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['41', '49'])).
% 0.59/0.77  thf('51', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.59/0.77           = (k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['25', '50'])).
% 0.59/0.77  thf('52', plain,
% 0.59/0.77      (![X17 : $i, X18 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.77           = (k3_xboole_0 @ X17 @ X18))),
% 0.59/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.77  thf('53', plain,
% 0.59/0.77      (![X10 : $i, X11 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X10 @ X11)
% 0.59/0.77           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.77  thf('54', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.59/0.77  thf('55', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X0 @ X1)
% 0.59/0.77           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.77  thf('56', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.59/0.77           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['54', '55'])).
% 0.59/0.77  thf('57', plain,
% 0.59/0.77      (![X22 : $i, X23 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X22 @ X23)
% 0.59/0.77           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.59/0.77  thf('58', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.77      inference('demod', [status(thm)], ['56', '57'])).
% 0.59/0.77  thf('59', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_boole])).
% 0.59/0.77  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['58', '59'])).
% 0.59/0.77  thf('61', plain,
% 0.59/0.77      (![X17 : $i, X18 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.77           = (k3_xboole_0 @ X17 @ X18))),
% 0.59/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.77  thf('62', plain,
% 0.59/0.77      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['60', '61'])).
% 0.59/0.77  thf('63', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.59/0.77  thf('64', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.77  thf('65', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['63', '64'])).
% 0.59/0.77  thf('66', plain,
% 0.59/0.77      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['62', '65'])).
% 0.59/0.77  thf('67', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.59/0.77           = (k5_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['41', '49'])).
% 0.59/0.77  thf('68', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.59/0.77           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['32', '33'])).
% 0.59/0.77  thf('69', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 0.59/0.77           (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.59/0.77           = (k5_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['67', '68'])).
% 0.59/0.77  thf('70', plain,
% 0.59/0.77      (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['39', '40'])).
% 0.59/0.77  thf('71', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.59/0.77           = (k5_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['41', '49'])).
% 0.59/0.77  thf('72', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.59/0.77           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.59/0.77  thf('73', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['58', '59'])).
% 0.59/0.77  thf('74', plain,
% 0.59/0.77      (![X22 : $i, X23 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X22 @ X23)
% 0.59/0.77           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.59/0.77  thf('75', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['73', '74'])).
% 0.59/0.77  thf('76', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.59/0.77           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['72', '75'])).
% 0.59/0.77  thf('77', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.59/0.77  thf(t22_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.59/0.77  thf('78', plain,
% 0.59/0.77      (![X13 : $i, X14 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)) = (X13))),
% 0.59/0.77      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.59/0.77  thf('79', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.59/0.77           = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['77', '78'])).
% 0.59/0.77  thf('80', plain,
% 0.59/0.77      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['76', '79'])).
% 0.59/0.77  thf('81', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.77      inference('demod', [status(thm)], ['66', '80'])).
% 0.59/0.77  thf('82', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k1_xboole_0)
% 0.59/0.77           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.59/0.77      inference('demod', [status(thm)], ['24', '81'])).
% 0.59/0.77  thf('83', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.59/0.77           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['32', '33'])).
% 0.59/0.77  thf('84', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.77      inference('demod', [status(thm)], ['66', '80'])).
% 0.59/0.77  thf('85', plain,
% 0.59/0.77      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['62', '65'])).
% 0.59/0.77  thf('86', plain,
% 0.59/0.77      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.59/0.77  thf('87', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['85', '86'])).
% 0.59/0.77  thf('88', plain,
% 0.59/0.77      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['76', '79'])).
% 0.59/0.77  thf('89', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['87', '88'])).
% 0.59/0.77  thf('90', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.59/0.77      inference('sup+', [status(thm)], ['84', '89'])).
% 0.59/0.77  thf('91', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.59/0.77      inference('demod', [status(thm)], ['83', '90'])).
% 0.59/0.77  thf('92', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.59/0.77           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['82', '91'])).
% 0.59/0.77  thf('93', plain,
% 0.59/0.77      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['76', '79'])).
% 0.59/0.77  thf('94', plain,
% 0.59/0.77      (![X22 : $i, X23 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X22 @ X23)
% 0.59/0.77           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.59/0.77  thf('95', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['93', '94'])).
% 0.59/0.77  thf('96', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_boole])).
% 0.59/0.77  thf('97', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.77      inference('demod', [status(thm)], ['95', '96'])).
% 0.59/0.77  thf('98', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.59/0.77      inference('demod', [status(thm)], ['92', '97'])).
% 0.59/0.77  thf('99', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k5_xboole_0 @ (k1_tarski @ X0) @ 
% 0.59/0.77           (k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0)))
% 0.59/0.77           = (k2_tarski @ X0 @ X1))),
% 0.59/0.77      inference('sup+', [status(thm)], ['16', '98'])).
% 0.59/0.77  thf('100', plain,
% 0.59/0.77      (![X22 : $i, X23 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X22 @ X23)
% 0.59/0.77           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.59/0.77  thf(t42_enumset1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.59/0.77       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.59/0.77  thf('101', plain,
% 0.59/0.77      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.59/0.77         ((k1_enumset1 @ X35 @ X36 @ X37)
% 0.59/0.77           = (k2_xboole_0 @ (k1_tarski @ X35) @ (k2_tarski @ X36 @ X37)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.59/0.77  thf('102', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.59/0.77      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.59/0.77  thf('103', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['0', '102'])).
% 0.59/0.77  thf('104', plain, ($false), inference('simplify', [status(thm)], ['103'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
