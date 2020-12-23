%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P98Z6J30Rt

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:01 EST 2020

% Result     : Theorem 7.66s
% Output     : Refutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :  133 (1044 expanded)
%              Number of leaves         :   17 ( 329 expanded)
%              Depth                    :   20
%              Number of atoms          : 1434 (12439 expanded)
%              Number of equality atoms :  126 (1066 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t99_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_enumset1 @ A @ B @ C )
        = ( k1_enumset1 @ B @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t99_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_B @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X17 @ X18 @ X19 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X17 @ X18 @ X19 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','12','19'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['21'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('32',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 @ X1 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X0 @ X1 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','12','19'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X17 @ X18 @ X19 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38','43'])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X0 @ X1 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('60',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('63',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['63'])).

thf('65',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['63'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('73',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('80',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','81'])).

thf('83',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['0','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','12','19'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','12','19'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('98',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X17 @ X18 @ X19 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('103',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_enumset1 @ X0 @ X1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38','43'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['93','111'])).

thf('113',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['83','112'])).

thf('114',plain,(
    $false ),
    inference(simplify,[status(thm)],['113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P98Z6J30Rt
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:48:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 7.66/7.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.66/7.90  % Solved by: fo/fo7.sh
% 7.66/7.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.66/7.90  % done 2597 iterations in 7.440s
% 7.66/7.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.66/7.90  % SZS output start Refutation
% 7.66/7.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.66/7.90  thf(sk_A_type, type, sk_A: $i).
% 7.66/7.90  thf(sk_C_type, type, sk_C: $i).
% 7.66/7.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.66/7.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.66/7.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.66/7.90  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 7.66/7.90  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 7.66/7.90  thf(sk_B_type, type, sk_B: $i).
% 7.66/7.90  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 7.66/7.90  thf(t99_enumset1, conjecture,
% 7.66/7.90    (![A:$i,B:$i,C:$i]:
% 7.66/7.90     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ))).
% 7.66/7.90  thf(zf_stmt_0, negated_conjecture,
% 7.66/7.90    (~( ![A:$i,B:$i,C:$i]:
% 7.66/7.90        ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ) )),
% 7.66/7.90    inference('cnf.neg', [status(esa)], [t99_enumset1])).
% 7.66/7.90  thf('0', plain,
% 7.66/7.90      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 7.66/7.90         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 7.66/7.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.90  thf(t69_enumset1, axiom,
% 7.66/7.90    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 7.66/7.90  thf('1', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 7.66/7.90      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.66/7.90  thf(t70_enumset1, axiom,
% 7.66/7.90    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 7.66/7.90  thf('2', plain,
% 7.66/7.90      (![X15 : $i, X16 : $i]:
% 7.66/7.90         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 7.66/7.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.66/7.90  thf(t44_enumset1, axiom,
% 7.66/7.90    (![A:$i,B:$i,C:$i,D:$i]:
% 7.66/7.90     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 7.66/7.90       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 7.66/7.90  thf('3', plain,
% 7.66/7.90      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 7.66/7.90      inference('cnf', [status(esa)], [t44_enumset1])).
% 7.66/7.90  thf('4', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['2', '3'])).
% 7.66/7.90  thf('5', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['1', '4'])).
% 7.66/7.90  thf(t71_enumset1, axiom,
% 7.66/7.90    (![A:$i,B:$i,C:$i]:
% 7.66/7.90     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 7.66/7.90  thf('6', plain,
% 7.66/7.90      (![X17 : $i, X18 : $i, X19 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 7.66/7.90           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 7.66/7.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.66/7.90  thf(t46_enumset1, axiom,
% 7.66/7.90    (![A:$i,B:$i,C:$i,D:$i]:
% 7.66/7.90     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 7.66/7.90       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 7.66/7.90  thf('7', plain,
% 7.66/7.90      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 7.66/7.90           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ (k1_tarski @ X13)))),
% 7.66/7.90      inference('cnf', [status(esa)], [t46_enumset1])).
% 7.66/7.90  thf('8', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 7.66/7.90           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 7.66/7.90              (k1_tarski @ X3)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['6', '7'])).
% 7.66/7.90  thf('9', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 7.66/7.90           = (k2_xboole_0 @ 
% 7.66/7.90              (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) @ 
% 7.66/7.90              (k1_tarski @ X1)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['5', '8'])).
% 7.66/7.90  thf('10', plain,
% 7.66/7.90      (![X17 : $i, X18 : $i, X19 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 7.66/7.90           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 7.66/7.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.66/7.90  thf('11', plain,
% 7.66/7.90      (![X15 : $i, X16 : $i]:
% 7.66/7.90         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 7.66/7.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.66/7.90  thf('12', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 7.66/7.90      inference('sup+', [status(thm)], ['10', '11'])).
% 7.66/7.90  thf('13', plain,
% 7.66/7.90      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 7.66/7.90      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.66/7.90  thf('14', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['2', '3'])).
% 7.66/7.90  thf('15', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 7.66/7.90      inference('sup+', [status(thm)], ['10', '11'])).
% 7.66/7.90  thf('16', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 7.66/7.90           = (k2_tarski @ X1 @ X0))),
% 7.66/7.90      inference('sup+', [status(thm)], ['14', '15'])).
% 7.66/7.90  thf('17', plain,
% 7.66/7.90      (![X0 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 7.66/7.90           = (k2_tarski @ X0 @ X0))),
% 7.66/7.90      inference('sup+', [status(thm)], ['13', '16'])).
% 7.66/7.90  thf('18', plain,
% 7.66/7.90      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 7.66/7.90      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.66/7.90  thf('19', plain,
% 7.66/7.90      (![X0 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 7.66/7.90           = (k1_tarski @ X0))),
% 7.66/7.90      inference('demod', [status(thm)], ['17', '18'])).
% 7.66/7.90  thf('20', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_tarski @ X0 @ X1)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 7.66/7.90      inference('demod', [status(thm)], ['9', '12', '19'])).
% 7.66/7.90  thf(d3_xboole_0, axiom,
% 7.66/7.90    (![A:$i,B:$i,C:$i]:
% 7.66/7.90     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 7.66/7.90       ( ![D:$i]:
% 7.66/7.90         ( ( r2_hidden @ D @ C ) <=>
% 7.66/7.90           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 7.66/7.90  thf('21', plain,
% 7.66/7.90      (![X1 : $i, X3 : $i, X5 : $i]:
% 7.66/7.90         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 7.66/7.90          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 7.66/7.90          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 7.66/7.90          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 7.66/7.90      inference('cnf', [status(esa)], [d3_xboole_0])).
% 7.66/7.90  thf('22', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 7.66/7.90          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 7.66/7.90          | ((X0) = (k2_xboole_0 @ X0 @ X1)))),
% 7.66/7.90      inference('eq_fact', [status(thm)], ['21'])).
% 7.66/7.90  thf('23', plain,
% 7.66/7.90      (![X1 : $i, X3 : $i, X5 : $i]:
% 7.66/7.90         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 7.66/7.90          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 7.66/7.90          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 7.66/7.90      inference('cnf', [status(esa)], [d3_xboole_0])).
% 7.66/7.90  thf('24', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 7.66/7.90          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 7.66/7.90          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 7.66/7.90          | ((X0) = (k2_xboole_0 @ X0 @ X1)))),
% 7.66/7.90      inference('sup-', [status(thm)], ['22', '23'])).
% 7.66/7.90  thf('25', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 7.66/7.90          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 7.66/7.90          | ((X0) = (k2_xboole_0 @ X0 @ X1)))),
% 7.66/7.90      inference('simplify', [status(thm)], ['24'])).
% 7.66/7.90  thf('26', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 7.66/7.90          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 7.66/7.90          | ((X0) = (k2_xboole_0 @ X0 @ X1)))),
% 7.66/7.90      inference('eq_fact', [status(thm)], ['21'])).
% 7.66/7.90  thf('27', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 7.66/7.90          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 7.66/7.90      inference('clc', [status(thm)], ['25', '26'])).
% 7.66/7.90  thf('28', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.66/7.90         (~ (r2_hidden @ X0 @ X1)
% 7.66/7.90          | (r2_hidden @ X0 @ X2)
% 7.66/7.90          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 7.66/7.90      inference('cnf', [status(esa)], [d3_xboole_0])).
% 7.66/7.90  thf('29', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X3 : $i]:
% 7.66/7.90         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 7.66/7.90      inference('simplify', [status(thm)], ['28'])).
% 7.66/7.90  thf('30', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 7.66/7.90          | (r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0)))),
% 7.66/7.90      inference('sup-', [status(thm)], ['27', '29'])).
% 7.66/7.90  thf('31', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 7.66/7.90          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 7.66/7.90      inference('clc', [status(thm)], ['25', '26'])).
% 7.66/7.90  thf('32', plain,
% 7.66/7.90      (![X1 : $i, X3 : $i, X5 : $i]:
% 7.66/7.90         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 7.66/7.90          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 7.66/7.90          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 7.66/7.90      inference('cnf', [status(esa)], [d3_xboole_0])).
% 7.66/7.90  thf('33', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 7.66/7.90          | ~ (r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ X1)
% 7.66/7.90          | ((X1) = (k2_xboole_0 @ X1 @ X0)))),
% 7.66/7.90      inference('sup-', [status(thm)], ['31', '32'])).
% 7.66/7.90  thf('34', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (~ (r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ X1)
% 7.66/7.90          | ((X1) = (k2_xboole_0 @ X1 @ X0)))),
% 7.66/7.90      inference('simplify', [status(thm)], ['33'])).
% 7.66/7.90  thf('35', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (((k2_xboole_0 @ X1 @ X0)
% 7.66/7.90            = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))
% 7.66/7.90          | ((k2_xboole_0 @ X1 @ X0)
% 7.66/7.90              = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 7.66/7.90      inference('sup-', [status(thm)], ['30', '34'])).
% 7.66/7.90  thf('36', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 7.66/7.90      inference('simplify', [status(thm)], ['35'])).
% 7.66/7.90  thf('37', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 7.66/7.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['20', '36'])).
% 7.66/7.90  thf('38', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_tarski @ X0 @ X1)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 7.66/7.90      inference('demod', [status(thm)], ['9', '12', '19'])).
% 7.66/7.90  thf('39', plain,
% 7.66/7.90      (![X15 : $i, X16 : $i]:
% 7.66/7.90         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 7.66/7.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.66/7.90  thf('40', plain,
% 7.66/7.90      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 7.66/7.90           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ (k1_tarski @ X13)))),
% 7.66/7.90      inference('cnf', [status(esa)], [t46_enumset1])).
% 7.66/7.90  thf('41', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 7.66/7.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['39', '40'])).
% 7.66/7.90  thf('42', plain,
% 7.66/7.90      (![X17 : $i, X18 : $i, X19 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 7.66/7.90           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 7.66/7.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.66/7.90  thf('43', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.66/7.90           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.66/7.90      inference('sup+', [status(thm)], ['41', '42'])).
% 7.66/7.90  thf('44', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 7.66/7.90      inference('demod', [status(thm)], ['37', '38', '43'])).
% 7.66/7.90  thf('45', plain,
% 7.66/7.90      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 7.66/7.90           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ (k1_tarski @ X13)))),
% 7.66/7.90      inference('cnf', [status(esa)], [t46_enumset1])).
% 7.66/7.90  thf('46', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X1 @ X0 @ X0 @ X2)
% 7.66/7.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['44', '45'])).
% 7.66/7.90  thf('47', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.66/7.90           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.66/7.90      inference('sup+', [status(thm)], ['41', '42'])).
% 7.66/7.90  thf('48', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X1 @ X0 @ X0 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 7.66/7.90      inference('demod', [status(thm)], ['46', '47'])).
% 7.66/7.90  thf('49', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['2', '3'])).
% 7.66/7.90  thf('50', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k1_enumset1 @ X2 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['48', '49'])).
% 7.66/7.90  thf('51', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 7.66/7.90          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 7.66/7.90      inference('clc', [status(thm)], ['25', '26'])).
% 7.66/7.90  thf('52', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.66/7.90         (~ (r2_hidden @ X0 @ X3)
% 7.66/7.90          | (r2_hidden @ X0 @ X2)
% 7.66/7.90          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 7.66/7.90      inference('cnf', [status(esa)], [d3_xboole_0])).
% 7.66/7.90  thf('53', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X3 : $i]:
% 7.66/7.90         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 7.66/7.90      inference('simplify', [status(thm)], ['52'])).
% 7.66/7.90  thf('54', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 7.66/7.90          | (r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 7.66/7.90      inference('sup-', [status(thm)], ['51', '53'])).
% 7.66/7.90  thf('55', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (~ (r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ X1)
% 7.66/7.90          | ((X1) = (k2_xboole_0 @ X1 @ X0)))),
% 7.66/7.90      inference('simplify', [status(thm)], ['33'])).
% 7.66/7.90  thf('56', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (((k2_xboole_0 @ X1 @ X0)
% 7.66/7.90            = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 7.66/7.90          | ((k2_xboole_0 @ X1 @ X0)
% 7.66/7.90              = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 7.66/7.90      inference('sup-', [status(thm)], ['54', '55'])).
% 7.66/7.90  thf('57', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 7.66/7.90      inference('simplify', [status(thm)], ['56'])).
% 7.66/7.90  thf('58', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 7.66/7.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['50', '57'])).
% 7.66/7.90  thf('59', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k1_enumset1 @ X2 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['48', '49'])).
% 7.66/7.90  thf('60', plain,
% 7.66/7.90      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 7.66/7.90           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ (k1_tarski @ X13)))),
% 7.66/7.90      inference('cnf', [status(esa)], [t46_enumset1])).
% 7.66/7.90  thf('61', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X0 @ X2))),
% 7.66/7.90      inference('demod', [status(thm)], ['58', '59', '60'])).
% 7.66/7.90  thf('62', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.66/7.90           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.66/7.90      inference('sup+', [status(thm)], ['41', '42'])).
% 7.66/7.90  thf('63', plain,
% 7.66/7.90      (![X1 : $i, X3 : $i, X5 : $i]:
% 7.66/7.90         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 7.66/7.90          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 7.66/7.90          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 7.66/7.90          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 7.66/7.90      inference('cnf', [status(esa)], [d3_xboole_0])).
% 7.66/7.90  thf('64', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.66/7.90          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 7.66/7.90          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 7.66/7.90      inference('eq_fact', [status(thm)], ['63'])).
% 7.66/7.90  thf('65', plain,
% 7.66/7.90      (![X1 : $i, X3 : $i, X5 : $i]:
% 7.66/7.90         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 7.66/7.90          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 7.66/7.90          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 7.66/7.90      inference('cnf', [status(esa)], [d3_xboole_0])).
% 7.66/7.90  thf('66', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 7.66/7.90          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 7.66/7.90          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.66/7.90          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 7.66/7.90      inference('sup-', [status(thm)], ['64', '65'])).
% 7.66/7.90  thf('67', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.66/7.90          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 7.66/7.90          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 7.66/7.90      inference('simplify', [status(thm)], ['66'])).
% 7.66/7.90  thf('68', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.66/7.90          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 7.66/7.90          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 7.66/7.90      inference('eq_fact', [status(thm)], ['63'])).
% 7.66/7.90  thf('69', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 7.66/7.90          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 7.66/7.90      inference('clc', [status(thm)], ['67', '68'])).
% 7.66/7.90  thf('70', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X3 : $i]:
% 7.66/7.90         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 7.66/7.90      inference('simplify', [status(thm)], ['28'])).
% 7.66/7.90  thf('71', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 7.66/7.90          | (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 7.66/7.90      inference('sup-', [status(thm)], ['69', '70'])).
% 7.66/7.90  thf('72', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 7.66/7.90          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 7.66/7.90      inference('clc', [status(thm)], ['67', '68'])).
% 7.66/7.90  thf('73', plain,
% 7.66/7.90      (![X1 : $i, X3 : $i, X5 : $i]:
% 7.66/7.90         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 7.66/7.90          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 7.66/7.90          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 7.66/7.90      inference('cnf', [status(esa)], [d3_xboole_0])).
% 7.66/7.90  thf('74', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 7.66/7.90          | ~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 7.66/7.90          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 7.66/7.90      inference('sup-', [status(thm)], ['72', '73'])).
% 7.66/7.90  thf('75', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 7.66/7.90          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 7.66/7.90      inference('simplify', [status(thm)], ['74'])).
% 7.66/7.90  thf('76', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         (((k2_xboole_0 @ X1 @ X0)
% 7.66/7.90            = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 7.66/7.90          | ((k2_xboole_0 @ X1 @ X0)
% 7.66/7.90              = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 7.66/7.90      inference('sup-', [status(thm)], ['71', '75'])).
% 7.66/7.90  thf('77', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 7.66/7.90      inference('simplify', [status(thm)], ['76'])).
% 7.66/7.90  thf('78', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['62', '77'])).
% 7.66/7.90  thf('79', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.66/7.90           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.66/7.90      inference('sup+', [status(thm)], ['41', '42'])).
% 7.66/7.90  thf('80', plain,
% 7.66/7.90      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 7.66/7.90      inference('cnf', [status(esa)], [t44_enumset1])).
% 7.66/7.90  thf('81', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X2 @ X1 @ X0))),
% 7.66/7.90      inference('demod', [status(thm)], ['78', '79', '80'])).
% 7.66/7.90  thf('82', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.66/7.90      inference('sup+', [status(thm)], ['61', '81'])).
% 7.66/7.90  thf('83', plain,
% 7.66/7.90      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 7.66/7.90         != (k1_enumset1 @ sk_A @ sk_C @ sk_B))),
% 7.66/7.90      inference('demod', [status(thm)], ['0', '82'])).
% 7.66/7.90  thf('84', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_tarski @ X0 @ X1)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 7.66/7.90      inference('demod', [status(thm)], ['9', '12', '19'])).
% 7.66/7.90  thf('85', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 7.66/7.90      inference('simplify', [status(thm)], ['56'])).
% 7.66/7.90  thf('86', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 7.66/7.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['84', '85'])).
% 7.66/7.90  thf('87', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_tarski @ X0 @ X1)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 7.66/7.90      inference('demod', [status(thm)], ['9', '12', '19'])).
% 7.66/7.90  thf('88', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.66/7.90           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.66/7.90      inference('sup+', [status(thm)], ['41', '42'])).
% 7.66/7.90  thf('89', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X1))),
% 7.66/7.90      inference('demod', [status(thm)], ['86', '87', '88'])).
% 7.66/7.90  thf('90', plain,
% 7.66/7.90      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 7.66/7.90      inference('cnf', [status(esa)], [t44_enumset1])).
% 7.66/7.90  thf('91', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['89', '90'])).
% 7.66/7.90  thf('92', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k1_enumset1 @ X2 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['48', '49'])).
% 7.66/7.90  thf('93', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.66/7.90      inference('demod', [status(thm)], ['91', '92'])).
% 7.66/7.90  thf('94', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.66/7.90           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.66/7.90      inference('sup+', [status(thm)], ['41', '42'])).
% 7.66/7.90  thf('95', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 7.66/7.90      inference('simplify', [status(thm)], ['35'])).
% 7.66/7.90  thf('96', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.66/7.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X0)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['94', '95'])).
% 7.66/7.90  thf('97', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.66/7.90           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.66/7.90      inference('sup+', [status(thm)], ['41', '42'])).
% 7.66/7.90  thf('98', plain,
% 7.66/7.90      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 7.66/7.90           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ (k1_tarski @ X13)))),
% 7.66/7.90      inference('cnf', [status(esa)], [t46_enumset1])).
% 7.66/7.90  thf('99', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X0 @ X0))),
% 7.66/7.90      inference('demod', [status(thm)], ['96', '97', '98'])).
% 7.66/7.90  thf('100', plain,
% 7.66/7.90      (![X17 : $i, X18 : $i, X19 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 7.66/7.90           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 7.66/7.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.66/7.90  thf('101', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X0 @ X0))),
% 7.66/7.90      inference('sup+', [status(thm)], ['99', '100'])).
% 7.66/7.90  thf('102', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X2 @ X1 @ X0))),
% 7.66/7.90      inference('demod', [status(thm)], ['78', '79', '80'])).
% 7.66/7.90  thf('103', plain,
% 7.66/7.90      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 7.66/7.90      inference('cnf', [status(esa)], [t44_enumset1])).
% 7.66/7.90  thf('104', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 7.66/7.90              (k2_enumset1 @ X0 @ X2 @ X1 @ X0)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['102', '103'])).
% 7.66/7.90  thf('105', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 7.66/7.90              (k2_enumset1 @ X0 @ X1 @ X0 @ X0)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['101', '104'])).
% 7.66/7.90  thf('106', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 7.66/7.90      inference('demod', [status(thm)], ['37', '38', '43'])).
% 7.66/7.90  thf('107', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X2 @ X1 @ X0))),
% 7.66/7.90      inference('demod', [status(thm)], ['78', '79', '80'])).
% 7.66/7.90  thf('108', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i]:
% 7.66/7.90         ((k2_tarski @ X1 @ X0) = (k2_enumset1 @ X0 @ X1 @ X0 @ X0))),
% 7.66/7.90      inference('sup+', [status(thm)], ['106', '107'])).
% 7.66/7.90  thf('109', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 7.66/7.90      inference('demod', [status(thm)], ['105', '108'])).
% 7.66/7.90  thf('110', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k1_enumset1 @ X2 @ X1 @ X0)
% 7.66/7.90           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 7.66/7.90      inference('sup+', [status(thm)], ['48', '49'])).
% 7.66/7.90  thf('111', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.66/7.90      inference('demod', [status(thm)], ['109', '110'])).
% 7.66/7.90  thf('112', plain,
% 7.66/7.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.90         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 7.66/7.90      inference('sup+', [status(thm)], ['93', '111'])).
% 7.66/7.90  thf('113', plain,
% 7.66/7.90      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 7.66/7.90         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 7.66/7.90      inference('demod', [status(thm)], ['83', '112'])).
% 7.66/7.90  thf('114', plain, ($false), inference('simplify', [status(thm)], ['113'])).
% 7.66/7.90  
% 7.66/7.90  % SZS output end Refutation
% 7.66/7.90  
% 7.74/7.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
