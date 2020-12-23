%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tbYdGlO92G

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:22 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 346 expanded)
%              Number of leaves         :   25 ( 111 expanded)
%              Depth                    :   19
%              Number of atoms          :  627 (2683 expanded)
%              Number of equality atoms :   63 ( 248 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X32 != X34 )
      | ( r2_hidden @ X32 @ X33 )
      | ( X33
       != ( k2_tarski @ X34 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X31: $i,X34: $i] :
      ( r2_hidden @ X34 @ ( k2_tarski @ X34 @ X31 ) ) ),
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
    ! [X26: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( X29 = X26 )
      | ( X28
       != ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X26: $i,X29: $i] :
      ( ( X29 = X26 )
      | ~ ( r2_hidden @ X29 @ ( k1_tarski @ X26 ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['17','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['17','31'])).

thf('34',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['16','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('39',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('47',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('53',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['15','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','54'])).

thf('56',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('57',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_tarski @ X37 ) @ ( k2_tarski @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tbYdGlO92G
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.31/1.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.31/1.51  % Solved by: fo/fo7.sh
% 1.31/1.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.31/1.51  % done 2513 iterations in 1.060s
% 1.31/1.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.31/1.51  % SZS output start Refutation
% 1.31/1.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.31/1.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.31/1.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.31/1.51  thf(sk_B_type, type, sk_B: $i).
% 1.31/1.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.31/1.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.31/1.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.31/1.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.31/1.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.31/1.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.31/1.51  thf(sk_A_type, type, sk_A: $i).
% 1.31/1.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.31/1.51  thf(t70_enumset1, conjecture,
% 1.31/1.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.31/1.51  thf(zf_stmt_0, negated_conjecture,
% 1.31/1.52    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 1.31/1.52    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 1.31/1.52  thf('0', plain,
% 1.31/1.52      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 1.31/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.52  thf(d2_tarski, axiom,
% 1.31/1.52    (![A:$i,B:$i,C:$i]:
% 1.31/1.52     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.31/1.52       ( ![D:$i]:
% 1.31/1.52         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.31/1.52  thf('1', plain,
% 1.31/1.52      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.31/1.52         (((X32) != (X34))
% 1.31/1.52          | (r2_hidden @ X32 @ X33)
% 1.31/1.52          | ((X33) != (k2_tarski @ X34 @ X31)))),
% 1.31/1.52      inference('cnf', [status(esa)], [d2_tarski])).
% 1.31/1.52  thf('2', plain,
% 1.31/1.52      (![X31 : $i, X34 : $i]: (r2_hidden @ X34 @ (k2_tarski @ X34 @ X31))),
% 1.31/1.52      inference('simplify', [status(thm)], ['1'])).
% 1.31/1.52  thf(d3_tarski, axiom,
% 1.31/1.52    (![A:$i,B:$i]:
% 1.31/1.52     ( ( r1_tarski @ A @ B ) <=>
% 1.31/1.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.31/1.52  thf('3', plain,
% 1.31/1.52      (![X3 : $i, X5 : $i]:
% 1.31/1.52         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.31/1.52      inference('cnf', [status(esa)], [d3_tarski])).
% 1.31/1.52  thf(d1_tarski, axiom,
% 1.31/1.52    (![A:$i,B:$i]:
% 1.31/1.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.31/1.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.31/1.52  thf('4', plain,
% 1.31/1.52      (![X26 : $i, X28 : $i, X29 : $i]:
% 1.31/1.52         (~ (r2_hidden @ X29 @ X28)
% 1.31/1.52          | ((X29) = (X26))
% 1.31/1.52          | ((X28) != (k1_tarski @ X26)))),
% 1.31/1.52      inference('cnf', [status(esa)], [d1_tarski])).
% 1.31/1.52  thf('5', plain,
% 1.31/1.52      (![X26 : $i, X29 : $i]:
% 1.31/1.52         (((X29) = (X26)) | ~ (r2_hidden @ X29 @ (k1_tarski @ X26)))),
% 1.31/1.52      inference('simplify', [status(thm)], ['4'])).
% 1.31/1.52  thf('6', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.31/1.52          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['3', '5'])).
% 1.31/1.52  thf('7', plain,
% 1.31/1.52      (![X3 : $i, X5 : $i]:
% 1.31/1.52         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 1.31/1.52      inference('cnf', [status(esa)], [d3_tarski])).
% 1.31/1.52  thf('8', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (r2_hidden @ X0 @ X1)
% 1.31/1.52          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.31/1.52          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['6', '7'])).
% 1.31/1.52  thf('9', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.31/1.52      inference('simplify', [status(thm)], ['8'])).
% 1.31/1.52  thf('10', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['2', '9'])).
% 1.31/1.52  thf(t28_xboole_1, axiom,
% 1.31/1.52    (![A:$i,B:$i]:
% 1.31/1.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.31/1.52  thf('11', plain,
% 1.31/1.52      (![X19 : $i, X20 : $i]:
% 1.31/1.52         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 1.31/1.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.31/1.52  thf('12', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 1.31/1.52           = (k1_tarski @ X1))),
% 1.31/1.52      inference('sup-', [status(thm)], ['10', '11'])).
% 1.31/1.52  thf(commutativity_k3_xboole_0, axiom,
% 1.31/1.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.31/1.52  thf('13', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.31/1.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.31/1.52  thf(t100_xboole_1, axiom,
% 1.31/1.52    (![A:$i,B:$i]:
% 1.31/1.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.31/1.52  thf('14', plain,
% 1.31/1.52      (![X16 : $i, X17 : $i]:
% 1.31/1.52         ((k4_xboole_0 @ X16 @ X17)
% 1.31/1.52           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.31/1.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.31/1.52  thf('15', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((k4_xboole_0 @ X0 @ X1)
% 1.31/1.52           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.31/1.52      inference('sup+', [status(thm)], ['13', '14'])).
% 1.31/1.52  thf(t91_xboole_1, axiom,
% 1.31/1.52    (![A:$i,B:$i,C:$i]:
% 1.31/1.52     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.31/1.52       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.31/1.52  thf('16', plain,
% 1.31/1.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.31/1.52         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 1.31/1.52           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 1.31/1.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.31/1.52  thf('17', plain,
% 1.31/1.52      (![X3 : $i, X5 : $i]:
% 1.31/1.52         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.31/1.52      inference('cnf', [status(esa)], [d3_tarski])).
% 1.31/1.52  thf(d10_xboole_0, axiom,
% 1.31/1.52    (![A:$i,B:$i]:
% 1.31/1.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.31/1.52  thf('18', plain,
% 1.31/1.52      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 1.31/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.31/1.52  thf('19', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 1.31/1.52      inference('simplify', [status(thm)], ['18'])).
% 1.31/1.52  thf('20', plain,
% 1.31/1.52      (![X19 : $i, X20 : $i]:
% 1.31/1.52         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 1.31/1.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.31/1.52  thf('21', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['19', '20'])).
% 1.31/1.52  thf('22', plain,
% 1.31/1.52      (![X16 : $i, X17 : $i]:
% 1.31/1.52         ((k4_xboole_0 @ X16 @ X17)
% 1.31/1.52           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.31/1.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.31/1.52  thf('23', plain,
% 1.31/1.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.31/1.52      inference('sup+', [status(thm)], ['21', '22'])).
% 1.31/1.52  thf(d5_xboole_0, axiom,
% 1.31/1.52    (![A:$i,B:$i,C:$i]:
% 1.31/1.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.31/1.52       ( ![D:$i]:
% 1.31/1.52         ( ( r2_hidden @ D @ C ) <=>
% 1.31/1.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.31/1.52  thf('24', plain,
% 1.31/1.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.31/1.52         (~ (r2_hidden @ X10 @ X9)
% 1.31/1.52          | (r2_hidden @ X10 @ X7)
% 1.31/1.52          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.31/1.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.31/1.52  thf('25', plain,
% 1.31/1.52      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.31/1.52         ((r2_hidden @ X10 @ X7)
% 1.31/1.52          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.31/1.52      inference('simplify', [status(thm)], ['24'])).
% 1.31/1.52  thf('26', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['23', '25'])).
% 1.31/1.52  thf('27', plain,
% 1.31/1.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.31/1.52      inference('sup+', [status(thm)], ['21', '22'])).
% 1.31/1.52  thf('28', plain,
% 1.31/1.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.31/1.52         (~ (r2_hidden @ X10 @ X9)
% 1.31/1.52          | ~ (r2_hidden @ X10 @ X8)
% 1.31/1.52          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.31/1.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.31/1.52  thf('29', plain,
% 1.31/1.52      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.31/1.52         (~ (r2_hidden @ X10 @ X8)
% 1.31/1.52          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.31/1.52      inference('simplify', [status(thm)], ['28'])).
% 1.31/1.52  thf('30', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 1.31/1.52          | ~ (r2_hidden @ X1 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['27', '29'])).
% 1.31/1.52  thf('31', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 1.31/1.52      inference('clc', [status(thm)], ['26', '30'])).
% 1.31/1.52  thf('32', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 1.31/1.52      inference('sup-', [status(thm)], ['17', '31'])).
% 1.31/1.52  thf('33', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 1.31/1.52      inference('sup-', [status(thm)], ['17', '31'])).
% 1.31/1.52  thf('34', plain,
% 1.31/1.52      (![X13 : $i, X15 : $i]:
% 1.31/1.52         (((X13) = (X15))
% 1.31/1.52          | ~ (r1_tarski @ X15 @ X13)
% 1.31/1.52          | ~ (r1_tarski @ X13 @ X15))),
% 1.31/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.31/1.52  thf('35', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ X1 @ X1))
% 1.31/1.52          | ((X0) = (k5_xboole_0 @ X1 @ X1)))),
% 1.31/1.52      inference('sup-', [status(thm)], ['33', '34'])).
% 1.31/1.52  thf('36', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X1) = (k5_xboole_0 @ X0 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['32', '35'])).
% 1.31/1.52  thf('37', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.52         ((k5_xboole_0 @ X2 @ X2)
% 1.31/1.52           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 1.31/1.52      inference('sup+', [status(thm)], ['16', '36'])).
% 1.31/1.52  thf('38', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X1) = (k5_xboole_0 @ X0 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['32', '35'])).
% 1.31/1.52  thf('39', plain,
% 1.31/1.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.31/1.52         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 1.31/1.52           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 1.31/1.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.31/1.52  thf('40', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.52         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 1.31/1.52           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X2 @ X1)))),
% 1.31/1.52      inference('sup+', [status(thm)], ['38', '39'])).
% 1.31/1.52  thf('41', plain,
% 1.31/1.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.31/1.52         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 1.31/1.52           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 1.31/1.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.31/1.52  thf('42', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.52         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1))
% 1.31/1.52           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X2 @ X1)))),
% 1.31/1.52      inference('demod', [status(thm)], ['40', '41'])).
% 1.31/1.52  thf('43', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X1) = (k5_xboole_0 @ X0 @ X0))),
% 1.31/1.52      inference('sup-', [status(thm)], ['32', '35'])).
% 1.31/1.52  thf('44', plain,
% 1.31/1.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.31/1.52      inference('sup+', [status(thm)], ['21', '22'])).
% 1.31/1.52  thf(t98_xboole_1, axiom,
% 1.31/1.52    (![A:$i,B:$i]:
% 1.31/1.52     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.31/1.52  thf('45', plain,
% 1.31/1.52      (![X24 : $i, X25 : $i]:
% 1.31/1.52         ((k2_xboole_0 @ X24 @ X25)
% 1.31/1.52           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 1.31/1.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.31/1.52  thf('46', plain,
% 1.31/1.52      (![X0 : $i]:
% 1.31/1.52         ((k2_xboole_0 @ X0 @ X0)
% 1.31/1.52           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.31/1.52      inference('sup+', [status(thm)], ['44', '45'])).
% 1.31/1.52  thf(idempotence_k2_xboole_0, axiom,
% 1.31/1.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.31/1.52  thf('47', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ X12) = (X12))),
% 1.31/1.52      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.31/1.52  thf('48', plain,
% 1.31/1.52      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.31/1.52      inference('demod', [status(thm)], ['46', '47'])).
% 1.31/1.52  thf('49', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((X1) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.31/1.52      inference('sup+', [status(thm)], ['43', '48'])).
% 1.31/1.52  thf('50', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.31/1.52      inference('sup+', [status(thm)], ['42', '49'])).
% 1.31/1.52  thf('51', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.52         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ X1))
% 1.31/1.52           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.31/1.52      inference('sup+', [status(thm)], ['37', '50'])).
% 1.31/1.52  thf('52', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((X1) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.31/1.52      inference('sup+', [status(thm)], ['43', '48'])).
% 1.31/1.52  thf('53', plain,
% 1.31/1.52      (![X1 : $i, X2 : $i]:
% 1.31/1.52         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ X1)) = (X2))),
% 1.31/1.52      inference('demod', [status(thm)], ['51', '52'])).
% 1.31/1.52  thf('54', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 1.31/1.52           = (X1))),
% 1.31/1.52      inference('sup+', [status(thm)], ['15', '53'])).
% 1.31/1.52  thf('55', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((k5_xboole_0 @ (k1_tarski @ X0) @ 
% 1.31/1.52           (k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0)))
% 1.31/1.52           = (k2_tarski @ X0 @ X1))),
% 1.31/1.52      inference('sup+', [status(thm)], ['12', '54'])).
% 1.31/1.52  thf('56', plain,
% 1.31/1.52      (![X24 : $i, X25 : $i]:
% 1.31/1.52         ((k2_xboole_0 @ X24 @ X25)
% 1.31/1.52           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 1.31/1.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.31/1.52  thf(t42_enumset1, axiom,
% 1.31/1.52    (![A:$i,B:$i,C:$i]:
% 1.31/1.52     ( ( k1_enumset1 @ A @ B @ C ) =
% 1.31/1.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 1.31/1.52  thf('57', plain,
% 1.31/1.52      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.31/1.52         ((k1_enumset1 @ X37 @ X38 @ X39)
% 1.31/1.52           = (k2_xboole_0 @ (k1_tarski @ X37) @ (k2_tarski @ X38 @ X39)))),
% 1.31/1.52      inference('cnf', [status(esa)], [t42_enumset1])).
% 1.31/1.52  thf('58', plain,
% 1.31/1.52      (![X0 : $i, X1 : $i]:
% 1.31/1.52         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 1.31/1.52      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.31/1.52  thf('59', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 1.31/1.52      inference('demod', [status(thm)], ['0', '58'])).
% 1.31/1.52  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 1.31/1.52  
% 1.31/1.52  % SZS output end Refutation
% 1.31/1.52  
% 1.31/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
