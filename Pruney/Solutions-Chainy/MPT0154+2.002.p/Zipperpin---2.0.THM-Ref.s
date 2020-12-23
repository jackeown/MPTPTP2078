%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AyOGxUJnIX

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:21 EST 2020

% Result     : Theorem 2.27s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 456 expanded)
%              Number of leaves         :   29 ( 154 expanded)
%              Depth                    :   22
%              Number of atoms          :  841 (3543 expanded)
%              Number of equality atoms :   88 ( 351 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X34 != X36 )
      | ( r2_hidden @ X34 @ X35 )
      | ( X35
       != ( k2_tarski @ X36 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X33: $i,X36: $i] :
      ( r2_hidden @ X36 @ ( k2_tarski @ X36 @ X33 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( X31 = X28 )
      | ( X30
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('30',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('40',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('44',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('47',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('48',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('59',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('61',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ X14 )
      = X14 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['38','39','40','41','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('66',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','62'])).

thf('70',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('72',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','74'])).

thf('76',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','79'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('81',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X39 @ X40 @ X41 )
      = ( k2_xboole_0 @ ( k1_tarski @ X39 ) @ ( k2_tarski @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','84'])).

thf('86',plain,(
    $false ),
    inference(simplify,[status(thm)],['85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AyOGxUJnIX
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:41:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.27/2.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.27/2.51  % Solved by: fo/fo7.sh
% 2.27/2.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.27/2.51  % done 1713 iterations in 2.047s
% 2.27/2.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.27/2.51  % SZS output start Refutation
% 2.27/2.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.27/2.51  thf(sk_B_type, type, sk_B: $i).
% 2.27/2.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.27/2.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.27/2.51  thf(sk_A_type, type, sk_A: $i).
% 2.27/2.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.27/2.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.27/2.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.27/2.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.27/2.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.27/2.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.27/2.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.27/2.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.27/2.51  thf(t70_enumset1, conjecture,
% 2.27/2.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.27/2.51  thf(zf_stmt_0, negated_conjecture,
% 2.27/2.51    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 2.27/2.51    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 2.27/2.51  thf('0', plain,
% 2.27/2.51      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 2.27/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.51  thf(d2_tarski, axiom,
% 2.27/2.51    (![A:$i,B:$i,C:$i]:
% 2.27/2.51     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 2.27/2.51       ( ![D:$i]:
% 2.27/2.51         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 2.27/2.51  thf('1', plain,
% 2.27/2.51      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.27/2.51         (((X34) != (X36))
% 2.27/2.51          | (r2_hidden @ X34 @ X35)
% 2.27/2.51          | ((X35) != (k2_tarski @ X36 @ X33)))),
% 2.27/2.51      inference('cnf', [status(esa)], [d2_tarski])).
% 2.27/2.51  thf('2', plain,
% 2.27/2.51      (![X33 : $i, X36 : $i]: (r2_hidden @ X36 @ (k2_tarski @ X36 @ X33))),
% 2.27/2.51      inference('simplify', [status(thm)], ['1'])).
% 2.27/2.51  thf(d3_tarski, axiom,
% 2.27/2.51    (![A:$i,B:$i]:
% 2.27/2.51     ( ( r1_tarski @ A @ B ) <=>
% 2.27/2.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.27/2.51  thf('3', plain,
% 2.27/2.51      (![X5 : $i, X7 : $i]:
% 2.27/2.51         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 2.27/2.51      inference('cnf', [status(esa)], [d3_tarski])).
% 2.27/2.51  thf(d1_tarski, axiom,
% 2.27/2.51    (![A:$i,B:$i]:
% 2.27/2.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 2.27/2.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 2.27/2.51  thf('4', plain,
% 2.27/2.51      (![X28 : $i, X30 : $i, X31 : $i]:
% 2.27/2.51         (~ (r2_hidden @ X31 @ X30)
% 2.27/2.51          | ((X31) = (X28))
% 2.27/2.51          | ((X30) != (k1_tarski @ X28)))),
% 2.27/2.51      inference('cnf', [status(esa)], [d1_tarski])).
% 2.27/2.51  thf('5', plain,
% 2.27/2.51      (![X28 : $i, X31 : $i]:
% 2.27/2.51         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 2.27/2.51      inference('simplify', [status(thm)], ['4'])).
% 2.27/2.51  thf('6', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 2.27/2.51          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 2.27/2.51      inference('sup-', [status(thm)], ['3', '5'])).
% 2.27/2.51  thf('7', plain,
% 2.27/2.51      (![X5 : $i, X7 : $i]:
% 2.27/2.51         ((r1_tarski @ X5 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X5) @ X7))),
% 2.27/2.51      inference('cnf', [status(esa)], [d3_tarski])).
% 2.27/2.51  thf('8', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         (~ (r2_hidden @ X0 @ X1)
% 2.27/2.51          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 2.27/2.51          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 2.27/2.51      inference('sup-', [status(thm)], ['6', '7'])).
% 2.27/2.51  thf('9', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 2.27/2.51      inference('simplify', [status(thm)], ['8'])).
% 2.27/2.51  thf('10', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 2.27/2.51      inference('sup-', [status(thm)], ['2', '9'])).
% 2.27/2.51  thf(t28_xboole_1, axiom,
% 2.27/2.51    (![A:$i,B:$i]:
% 2.27/2.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.27/2.51  thf('11', plain,
% 2.27/2.51      (![X19 : $i, X20 : $i]:
% 2.27/2.51         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 2.27/2.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.27/2.51  thf('12', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 2.27/2.51           = (k1_tarski @ X1))),
% 2.27/2.51      inference('sup-', [status(thm)], ['10', '11'])).
% 2.27/2.51  thf(commutativity_k3_xboole_0, axiom,
% 2.27/2.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.27/2.51  thf('13', plain,
% 2.27/2.51      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.27/2.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.27/2.51  thf(t48_xboole_1, axiom,
% 2.27/2.51    (![A:$i,B:$i]:
% 2.27/2.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.27/2.51  thf('14', plain,
% 2.27/2.51      (![X21 : $i, X22 : $i]:
% 2.27/2.51         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 2.27/2.51           = (k3_xboole_0 @ X21 @ X22))),
% 2.27/2.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.27/2.51  thf('15', plain,
% 2.27/2.51      (![X5 : $i, X7 : $i]:
% 2.27/2.51         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 2.27/2.51      inference('cnf', [status(esa)], [d3_tarski])).
% 2.27/2.51  thf(d5_xboole_0, axiom,
% 2.27/2.51    (![A:$i,B:$i,C:$i]:
% 2.27/2.51     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.27/2.51       ( ![D:$i]:
% 2.27/2.51         ( ( r2_hidden @ D @ C ) <=>
% 2.27/2.51           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.27/2.51  thf('16', plain,
% 2.27/2.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.27/2.51         (~ (r2_hidden @ X12 @ X11)
% 2.27/2.51          | (r2_hidden @ X12 @ X9)
% 2.27/2.51          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 2.27/2.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.27/2.51  thf('17', plain,
% 2.27/2.51      (![X9 : $i, X10 : $i, X12 : $i]:
% 2.27/2.51         ((r2_hidden @ X12 @ X9)
% 2.27/2.51          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.27/2.51      inference('simplify', [status(thm)], ['16'])).
% 2.27/2.51  thf('18', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.27/2.51         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 2.27/2.51          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 2.27/2.51      inference('sup-', [status(thm)], ['15', '17'])).
% 2.27/2.51  thf('19', plain,
% 2.27/2.51      (![X5 : $i, X7 : $i]:
% 2.27/2.51         ((r1_tarski @ X5 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X5) @ X7))),
% 2.27/2.51      inference('cnf', [status(esa)], [d3_tarski])).
% 2.27/2.51  thf('20', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 2.27/2.51          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 2.27/2.51      inference('sup-', [status(thm)], ['18', '19'])).
% 2.27/2.51  thf('21', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 2.27/2.51      inference('simplify', [status(thm)], ['20'])).
% 2.27/2.51  thf('22', plain,
% 2.27/2.51      (![X19 : $i, X20 : $i]:
% 2.27/2.51         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 2.27/2.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.27/2.51  thf('23', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 2.27/2.51           = (k4_xboole_0 @ X0 @ X1))),
% 2.27/2.51      inference('sup-', [status(thm)], ['21', '22'])).
% 2.27/2.51  thf('24', plain,
% 2.27/2.51      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.27/2.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.27/2.51  thf('25', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.27/2.51           = (k4_xboole_0 @ X0 @ X1))),
% 2.27/2.51      inference('demod', [status(thm)], ['23', '24'])).
% 2.27/2.51  thf('26', plain,
% 2.27/2.51      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.27/2.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.27/2.51  thf(t100_xboole_1, axiom,
% 2.27/2.51    (![A:$i,B:$i]:
% 2.27/2.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.27/2.51  thf('27', plain,
% 2.27/2.51      (![X16 : $i, X17 : $i]:
% 2.27/2.51         ((k4_xboole_0 @ X16 @ X17)
% 2.27/2.51           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 2.27/2.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.27/2.51  thf('28', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k4_xboole_0 @ X0 @ X1)
% 2.27/2.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.27/2.51      inference('sup+', [status(thm)], ['26', '27'])).
% 2.27/2.51  thf('29', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 2.27/2.51           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 2.27/2.51      inference('sup+', [status(thm)], ['25', '28'])).
% 2.27/2.51  thf(idempotence_k3_xboole_0, axiom,
% 2.27/2.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 2.27/2.51  thf('30', plain, (![X15 : $i]: ((k3_xboole_0 @ X15 @ X15) = (X15))),
% 2.27/2.51      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.27/2.51  thf('31', plain,
% 2.27/2.51      (![X16 : $i, X17 : $i]:
% 2.27/2.51         ((k4_xboole_0 @ X16 @ X17)
% 2.27/2.51           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 2.27/2.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.27/2.51  thf('32', plain,
% 2.27/2.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['30', '31'])).
% 2.27/2.51  thf('33', plain,
% 2.27/2.51      (![X21 : $i, X22 : $i]:
% 2.27/2.51         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 2.27/2.51           = (k3_xboole_0 @ X21 @ X22))),
% 2.27/2.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.27/2.51  thf(t98_xboole_1, axiom,
% 2.27/2.51    (![A:$i,B:$i]:
% 2.27/2.51     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.27/2.51  thf('34', plain,
% 2.27/2.51      (![X26 : $i, X27 : $i]:
% 2.27/2.51         ((k2_xboole_0 @ X26 @ X27)
% 2.27/2.51           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 2.27/2.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.27/2.51  thf('35', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 2.27/2.51           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.27/2.51      inference('sup+', [status(thm)], ['33', '34'])).
% 2.27/2.51  thf(commutativity_k2_xboole_0, axiom,
% 2.27/2.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.27/2.51  thf('36', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.27/2.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.27/2.51  thf('37', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 2.27/2.51           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.27/2.51      inference('demod', [status(thm)], ['35', '36'])).
% 2.27/2.51  thf('38', plain,
% 2.27/2.51      (![X0 : $i]:
% 2.27/2.51         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 2.27/2.51           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0)))),
% 2.27/2.51      inference('sup+', [status(thm)], ['32', '37'])).
% 2.27/2.51  thf('39', plain,
% 2.27/2.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['30', '31'])).
% 2.27/2.51  thf('40', plain, (![X15 : $i]: ((k3_xboole_0 @ X15 @ X15) = (X15))),
% 2.27/2.51      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.27/2.51  thf(t91_xboole_1, axiom,
% 2.27/2.51    (![A:$i,B:$i,C:$i]:
% 2.27/2.51     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 2.27/2.51       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 2.27/2.51  thf('41', plain,
% 2.27/2.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.27/2.51         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 2.27/2.51           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 2.27/2.51      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.27/2.51  thf('42', plain,
% 2.27/2.51      (![X5 : $i, X7 : $i]:
% 2.27/2.51         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 2.27/2.51      inference('cnf', [status(esa)], [d3_tarski])).
% 2.27/2.51  thf('43', plain,
% 2.27/2.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['30', '31'])).
% 2.27/2.51  thf('44', plain,
% 2.27/2.51      (![X9 : $i, X10 : $i, X12 : $i]:
% 2.27/2.51         ((r2_hidden @ X12 @ X9)
% 2.27/2.51          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.27/2.51      inference('simplify', [status(thm)], ['16'])).
% 2.27/2.51  thf('45', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 2.27/2.51      inference('sup-', [status(thm)], ['43', '44'])).
% 2.27/2.51  thf('46', plain,
% 2.27/2.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['30', '31'])).
% 2.27/2.51  thf('47', plain,
% 2.27/2.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.27/2.51         (~ (r2_hidden @ X12 @ X11)
% 2.27/2.51          | ~ (r2_hidden @ X12 @ X10)
% 2.27/2.51          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 2.27/2.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.27/2.51  thf('48', plain,
% 2.27/2.51      (![X9 : $i, X10 : $i, X12 : $i]:
% 2.27/2.51         (~ (r2_hidden @ X12 @ X10)
% 2.27/2.51          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.27/2.51      inference('simplify', [status(thm)], ['47'])).
% 2.27/2.51  thf('49', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 2.27/2.51          | ~ (r2_hidden @ X1 @ X0))),
% 2.27/2.51      inference('sup-', [status(thm)], ['46', '48'])).
% 2.27/2.51  thf('50', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 2.27/2.51      inference('clc', [status(thm)], ['45', '49'])).
% 2.27/2.51  thf('51', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 2.27/2.51      inference('sup-', [status(thm)], ['42', '50'])).
% 2.27/2.51  thf('52', plain,
% 2.27/2.51      (![X19 : $i, X20 : $i]:
% 2.27/2.51         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 2.27/2.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.27/2.51  thf('53', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 2.27/2.51           = (k5_xboole_0 @ X1 @ X1))),
% 2.27/2.51      inference('sup-', [status(thm)], ['51', '52'])).
% 2.27/2.51  thf('54', plain,
% 2.27/2.51      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.27/2.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.27/2.51  thf('55', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 2.27/2.51           = (k5_xboole_0 @ X0 @ X0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['53', '54'])).
% 2.27/2.51  thf('56', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 2.27/2.51           = (k5_xboole_0 @ X1 @ X1))),
% 2.27/2.51      inference('sup-', [status(thm)], ['51', '52'])).
% 2.27/2.51  thf('57', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X1 @ X1))),
% 2.27/2.51      inference('sup+', [status(thm)], ['55', '56'])).
% 2.27/2.51  thf('58', plain,
% 2.27/2.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['30', '31'])).
% 2.27/2.51  thf('59', plain,
% 2.27/2.51      (![X26 : $i, X27 : $i]:
% 2.27/2.51         ((k2_xboole_0 @ X26 @ X27)
% 2.27/2.51           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 2.27/2.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.27/2.51  thf('60', plain,
% 2.27/2.51      (![X0 : $i]:
% 2.27/2.51         ((k2_xboole_0 @ X0 @ X0)
% 2.27/2.51           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 2.27/2.51      inference('sup+', [status(thm)], ['58', '59'])).
% 2.27/2.51  thf(idempotence_k2_xboole_0, axiom,
% 2.27/2.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 2.27/2.51  thf('61', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ X14) = (X14))),
% 2.27/2.51      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.27/2.51  thf('62', plain,
% 2.27/2.51      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 2.27/2.51      inference('demod', [status(thm)], ['60', '61'])).
% 2.27/2.51  thf('63', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((X1) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 2.27/2.51      inference('sup+', [status(thm)], ['57', '62'])).
% 2.27/2.51  thf('64', plain,
% 2.27/2.51      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 2.27/2.51      inference('demod', [status(thm)], ['38', '39', '40', '41', '63'])).
% 2.27/2.51  thf('65', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.27/2.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.27/2.51  thf(t1_boole, axiom,
% 2.27/2.51    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.27/2.51  thf('66', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 2.27/2.51      inference('cnf', [status(esa)], [t1_boole])).
% 2.27/2.51  thf('67', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['65', '66'])).
% 2.27/2.51  thf('68', plain,
% 2.27/2.51      (((k1_xboole_0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['64', '67'])).
% 2.27/2.51  thf('69', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((X1) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 2.27/2.51      inference('sup+', [status(thm)], ['57', '62'])).
% 2.27/2.51  thf('70', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['68', '69'])).
% 2.27/2.51  thf('71', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X1 @ X1))),
% 2.27/2.51      inference('sup+', [status(thm)], ['55', '56'])).
% 2.27/2.51  thf('72', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['70', '71'])).
% 2.27/2.51  thf('73', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 2.27/2.51      inference('demod', [status(thm)], ['29', '72'])).
% 2.27/2.51  thf('74', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['14', '73'])).
% 2.27/2.51  thf('75', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['13', '74'])).
% 2.27/2.51  thf('76', plain,
% 2.27/2.51      (![X26 : $i, X27 : $i]:
% 2.27/2.51         ((k2_xboole_0 @ X26 @ X27)
% 2.27/2.51           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 2.27/2.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.27/2.51  thf('77', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.27/2.51           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['75', '76'])).
% 2.27/2.51  thf('78', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['68', '69'])).
% 2.27/2.51  thf('79', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 2.27/2.51      inference('demod', [status(thm)], ['77', '78'])).
% 2.27/2.51  thf('80', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))
% 2.27/2.51           = (k2_tarski @ X0 @ X1))),
% 2.27/2.51      inference('sup+', [status(thm)], ['12', '79'])).
% 2.27/2.51  thf(t42_enumset1, axiom,
% 2.27/2.51    (![A:$i,B:$i,C:$i]:
% 2.27/2.51     ( ( k1_enumset1 @ A @ B @ C ) =
% 2.27/2.51       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 2.27/2.51  thf('81', plain,
% 2.27/2.51      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.27/2.51         ((k1_enumset1 @ X39 @ X40 @ X41)
% 2.27/2.51           = (k2_xboole_0 @ (k1_tarski @ X39) @ (k2_tarski @ X40 @ X41)))),
% 2.27/2.51      inference('cnf', [status(esa)], [t42_enumset1])).
% 2.27/2.51  thf('82', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.27/2.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.27/2.51  thf('83', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.27/2.51         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 2.27/2.51           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.27/2.51      inference('sup+', [status(thm)], ['81', '82'])).
% 2.27/2.51  thf('84', plain,
% 2.27/2.51      (![X0 : $i, X1 : $i]:
% 2.27/2.51         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 2.27/2.51      inference('demod', [status(thm)], ['80', '83'])).
% 2.27/2.51  thf('85', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 2.27/2.51      inference('demod', [status(thm)], ['0', '84'])).
% 2.27/2.51  thf('86', plain, ($false), inference('simplify', [status(thm)], ['85'])).
% 2.27/2.51  
% 2.27/2.51  % SZS output end Refutation
% 2.27/2.51  
% 2.27/2.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
