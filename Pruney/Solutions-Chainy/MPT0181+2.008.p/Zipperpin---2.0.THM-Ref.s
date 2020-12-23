%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UVN2bUS7ZG

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:58 EST 2020

% Result     : Theorem 8.64s
% Output     : Refutation 8.64s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 686 expanded)
%              Number of leaves         :   17 ( 219 expanded)
%              Depth                    :   18
%              Number of atoms          : 1338 (8089 expanded)
%              Number of equality atoms :  117 ( 696 expanded)
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

thf(t98_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_enumset1 @ A @ B @ C )
        = ( k1_enumset1 @ A @ C @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t98_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_C @ sk_B ) ),
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
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
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
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
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
      = ( k1_enumset1 @ X1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38','43'])).

thf('45',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','12','19'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X0 @ X1 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','12','19'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('70',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X17 @ X18 @ X19 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('75',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['75'])).

thf('77',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['75'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('85',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('92',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_enumset1 @ X0 @ X1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','102'])).

thf('104',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','103'])).

thf('105',plain,(
    $false ),
    inference(simplify,[status(thm)],['104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UVN2bUS7ZG
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.64/8.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.64/8.85  % Solved by: fo/fo7.sh
% 8.64/8.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.64/8.85  % done 2596 iterations in 8.392s
% 8.64/8.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.64/8.85  % SZS output start Refutation
% 8.64/8.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.64/8.85  thf(sk_A_type, type, sk_A: $i).
% 8.64/8.85  thf(sk_C_type, type, sk_C: $i).
% 8.64/8.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.64/8.85  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 8.64/8.85  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.64/8.85  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 8.64/8.85  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 8.64/8.85  thf(sk_B_type, type, sk_B: $i).
% 8.64/8.85  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 8.64/8.85  thf(t98_enumset1, conjecture,
% 8.64/8.85    (![A:$i,B:$i,C:$i]:
% 8.64/8.85     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 8.64/8.85  thf(zf_stmt_0, negated_conjecture,
% 8.64/8.85    (~( ![A:$i,B:$i,C:$i]:
% 8.64/8.85        ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ) )),
% 8.64/8.85    inference('cnf.neg', [status(esa)], [t98_enumset1])).
% 8.64/8.85  thf('0', plain,
% 8.64/8.85      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 8.64/8.85         != (k1_enumset1 @ sk_A @ sk_C @ sk_B))),
% 8.64/8.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.85  thf(t69_enumset1, axiom,
% 8.64/8.85    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 8.64/8.85  thf('1', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 8.64/8.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 8.64/8.85  thf(t70_enumset1, axiom,
% 8.64/8.85    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 8.64/8.85  thf('2', plain,
% 8.64/8.85      (![X15 : $i, X16 : $i]:
% 8.64/8.85         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 8.64/8.85      inference('cnf', [status(esa)], [t70_enumset1])).
% 8.64/8.85  thf(t44_enumset1, axiom,
% 8.64/8.85    (![A:$i,B:$i,C:$i,D:$i]:
% 8.64/8.85     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 8.64/8.85       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 8.64/8.85  thf('3', plain,
% 8.64/8.85      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 8.64/8.85      inference('cnf', [status(esa)], [t44_enumset1])).
% 8.64/8.85  thf('4', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['2', '3'])).
% 8.64/8.85  thf('5', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['1', '4'])).
% 8.64/8.85  thf(t71_enumset1, axiom,
% 8.64/8.85    (![A:$i,B:$i,C:$i]:
% 8.64/8.85     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 8.64/8.85  thf('6', plain,
% 8.64/8.85      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 8.64/8.85           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 8.64/8.85      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.64/8.85  thf(t46_enumset1, axiom,
% 8.64/8.85    (![A:$i,B:$i,C:$i,D:$i]:
% 8.64/8.85     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 8.64/8.85       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 8.64/8.85  thf('7', plain,
% 8.64/8.85      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 8.64/8.85           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ (k1_tarski @ X13)))),
% 8.64/8.85      inference('cnf', [status(esa)], [t46_enumset1])).
% 8.64/8.85  thf('8', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 8.64/8.85           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 8.64/8.85              (k1_tarski @ X3)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['6', '7'])).
% 8.64/8.85  thf('9', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 8.64/8.85           = (k2_xboole_0 @ 
% 8.64/8.85              (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) @ 
% 8.64/8.85              (k1_tarski @ X1)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['5', '8'])).
% 8.64/8.85  thf('10', plain,
% 8.64/8.85      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 8.64/8.85           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 8.64/8.85      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.64/8.85  thf('11', plain,
% 8.64/8.85      (![X15 : $i, X16 : $i]:
% 8.64/8.85         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 8.64/8.85      inference('cnf', [status(esa)], [t70_enumset1])).
% 8.64/8.85  thf('12', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 8.64/8.85      inference('sup+', [status(thm)], ['10', '11'])).
% 8.64/8.85  thf('13', plain,
% 8.64/8.85      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 8.64/8.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 8.64/8.85  thf('14', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['2', '3'])).
% 8.64/8.85  thf('15', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 8.64/8.85      inference('sup+', [status(thm)], ['10', '11'])).
% 8.64/8.85  thf('16', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 8.64/8.85           = (k2_tarski @ X1 @ X0))),
% 8.64/8.85      inference('sup+', [status(thm)], ['14', '15'])).
% 8.64/8.85  thf('17', plain,
% 8.64/8.85      (![X0 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 8.64/8.85           = (k2_tarski @ X0 @ X0))),
% 8.64/8.85      inference('sup+', [status(thm)], ['13', '16'])).
% 8.64/8.85  thf('18', plain,
% 8.64/8.85      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 8.64/8.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 8.64/8.85  thf('19', plain,
% 8.64/8.85      (![X0 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 8.64/8.85           = (k1_tarski @ X0))),
% 8.64/8.85      inference('demod', [status(thm)], ['17', '18'])).
% 8.64/8.85  thf('20', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_tarski @ X0 @ X1)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 8.64/8.85      inference('demod', [status(thm)], ['9', '12', '19'])).
% 8.64/8.85  thf(d3_xboole_0, axiom,
% 8.64/8.85    (![A:$i,B:$i,C:$i]:
% 8.64/8.85     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 8.64/8.85       ( ![D:$i]:
% 8.64/8.85         ( ( r2_hidden @ D @ C ) <=>
% 8.64/8.85           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 8.64/8.85  thf('21', plain,
% 8.64/8.85      (![X1 : $i, X3 : $i, X5 : $i]:
% 8.64/8.85         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 8.64/8.85          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 8.64/8.85          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 8.64/8.85          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 8.64/8.85      inference('cnf', [status(esa)], [d3_xboole_0])).
% 8.64/8.85  thf('22', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 8.64/8.85          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 8.64/8.85          | ((X0) = (k2_xboole_0 @ X0 @ X1)))),
% 8.64/8.85      inference('eq_fact', [status(thm)], ['21'])).
% 8.64/8.85  thf('23', plain,
% 8.64/8.85      (![X1 : $i, X3 : $i, X5 : $i]:
% 8.64/8.85         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 8.64/8.85          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 8.64/8.85          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 8.64/8.85      inference('cnf', [status(esa)], [d3_xboole_0])).
% 8.64/8.85  thf('24', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 8.64/8.85          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 8.64/8.85          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 8.64/8.85          | ((X0) = (k2_xboole_0 @ X0 @ X1)))),
% 8.64/8.85      inference('sup-', [status(thm)], ['22', '23'])).
% 8.64/8.85  thf('25', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 8.64/8.85          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 8.64/8.85          | ((X0) = (k2_xboole_0 @ X0 @ X1)))),
% 8.64/8.85      inference('simplify', [status(thm)], ['24'])).
% 8.64/8.85  thf('26', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 8.64/8.85          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 8.64/8.85          | ((X0) = (k2_xboole_0 @ X0 @ X1)))),
% 8.64/8.85      inference('eq_fact', [status(thm)], ['21'])).
% 8.64/8.85  thf('27', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 8.64/8.85          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 8.64/8.85      inference('clc', [status(thm)], ['25', '26'])).
% 8.64/8.85  thf('28', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.64/8.85         (~ (r2_hidden @ X0 @ X3)
% 8.64/8.85          | (r2_hidden @ X0 @ X2)
% 8.64/8.85          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 8.64/8.85      inference('cnf', [status(esa)], [d3_xboole_0])).
% 8.64/8.85  thf('29', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X3 : $i]:
% 8.64/8.85         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 8.64/8.85      inference('simplify', [status(thm)], ['28'])).
% 8.64/8.85  thf('30', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 8.64/8.85          | (r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 8.64/8.85      inference('sup-', [status(thm)], ['27', '29'])).
% 8.64/8.85  thf('31', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 8.64/8.85          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 8.64/8.85      inference('clc', [status(thm)], ['25', '26'])).
% 8.64/8.85  thf('32', plain,
% 8.64/8.85      (![X1 : $i, X3 : $i, X5 : $i]:
% 8.64/8.85         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 8.64/8.85          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 8.64/8.85          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 8.64/8.85      inference('cnf', [status(esa)], [d3_xboole_0])).
% 8.64/8.85  thf('33', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 8.64/8.85          | ~ (r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ X1)
% 8.64/8.85          | ((X1) = (k2_xboole_0 @ X1 @ X0)))),
% 8.64/8.85      inference('sup-', [status(thm)], ['31', '32'])).
% 8.64/8.85  thf('34', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (~ (r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ X1)
% 8.64/8.85          | ((X1) = (k2_xboole_0 @ X1 @ X0)))),
% 8.64/8.85      inference('simplify', [status(thm)], ['33'])).
% 8.64/8.85  thf('35', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (((k2_xboole_0 @ X1 @ X0)
% 8.64/8.85            = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 8.64/8.85          | ((k2_xboole_0 @ X1 @ X0)
% 8.64/8.85              = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 8.64/8.85      inference('sup-', [status(thm)], ['30', '34'])).
% 8.64/8.85  thf('36', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ X1 @ X0)
% 8.64/8.85           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 8.64/8.85      inference('simplify', [status(thm)], ['35'])).
% 8.64/8.85  thf('37', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 8.64/8.85           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['20', '36'])).
% 8.64/8.85  thf('38', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_tarski @ X0 @ X1)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 8.64/8.85      inference('demod', [status(thm)], ['9', '12', '19'])).
% 8.64/8.85  thf('39', plain,
% 8.64/8.85      (![X15 : $i, X16 : $i]:
% 8.64/8.85         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 8.64/8.85      inference('cnf', [status(esa)], [t70_enumset1])).
% 8.64/8.85  thf('40', plain,
% 8.64/8.85      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 8.64/8.85           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ (k1_tarski @ X13)))),
% 8.64/8.85      inference('cnf', [status(esa)], [t46_enumset1])).
% 8.64/8.85  thf('41', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 8.64/8.85           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['39', '40'])).
% 8.64/8.85  thf('42', plain,
% 8.64/8.85      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 8.64/8.85           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 8.64/8.85      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.64/8.85  thf('43', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 8.64/8.85           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.64/8.85      inference('sup+', [status(thm)], ['41', '42'])).
% 8.64/8.85  thf('44', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X1))),
% 8.64/8.85      inference('demod', [status(thm)], ['37', '38', '43'])).
% 8.64/8.85  thf('45', plain,
% 8.64/8.85      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 8.64/8.85      inference('cnf', [status(esa)], [t44_enumset1])).
% 8.64/8.85  thf('46', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['44', '45'])).
% 8.64/8.85  thf('47', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_tarski @ X0 @ X1)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 8.64/8.85      inference('demod', [status(thm)], ['9', '12', '19'])).
% 8.64/8.85  thf('48', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 8.64/8.85          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 8.64/8.85      inference('clc', [status(thm)], ['25', '26'])).
% 8.64/8.85  thf('49', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.64/8.85         (~ (r2_hidden @ X0 @ X1)
% 8.64/8.85          | (r2_hidden @ X0 @ X2)
% 8.64/8.85          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 8.64/8.85      inference('cnf', [status(esa)], [d3_xboole_0])).
% 8.64/8.85  thf('50', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X3 : $i]:
% 8.64/8.85         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 8.64/8.85      inference('simplify', [status(thm)], ['49'])).
% 8.64/8.85  thf('51', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 8.64/8.85          | (r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0)))),
% 8.64/8.85      inference('sup-', [status(thm)], ['48', '50'])).
% 8.64/8.85  thf('52', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (~ (r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ X1)
% 8.64/8.85          | ((X1) = (k2_xboole_0 @ X1 @ X0)))),
% 8.64/8.85      inference('simplify', [status(thm)], ['33'])).
% 8.64/8.85  thf('53', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (((k2_xboole_0 @ X1 @ X0)
% 8.64/8.85            = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))
% 8.64/8.85          | ((k2_xboole_0 @ X1 @ X0)
% 8.64/8.85              = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 8.64/8.85      inference('sup-', [status(thm)], ['51', '52'])).
% 8.64/8.85  thf('54', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ X1 @ X0)
% 8.64/8.85           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 8.64/8.85      inference('simplify', [status(thm)], ['53'])).
% 8.64/8.85  thf('55', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 8.64/8.85           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['47', '54'])).
% 8.64/8.85  thf('56', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_tarski @ X0 @ X1)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 8.64/8.85      inference('demod', [status(thm)], ['9', '12', '19'])).
% 8.64/8.85  thf('57', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 8.64/8.85           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.64/8.85      inference('sup+', [status(thm)], ['41', '42'])).
% 8.64/8.85  thf('58', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 8.64/8.85      inference('demod', [status(thm)], ['55', '56', '57'])).
% 8.64/8.85  thf('59', plain,
% 8.64/8.85      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 8.64/8.85           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ (k1_tarski @ X13)))),
% 8.64/8.85      inference('cnf', [status(esa)], [t46_enumset1])).
% 8.64/8.85  thf('60', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X1 @ X0 @ X0 @ X2)
% 8.64/8.85           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['58', '59'])).
% 8.64/8.85  thf('61', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 8.64/8.85           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.64/8.85      inference('sup+', [status(thm)], ['41', '42'])).
% 8.64/8.85  thf('62', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X1 @ X0 @ X0 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 8.64/8.85      inference('demod', [status(thm)], ['60', '61'])).
% 8.64/8.85  thf('63', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['2', '3'])).
% 8.64/8.85  thf('64', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k1_enumset1 @ X2 @ X1 @ X0)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['62', '63'])).
% 8.64/8.85  thf('65', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.64/8.85      inference('demod', [status(thm)], ['46', '64'])).
% 8.64/8.85  thf('66', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 8.64/8.85           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.64/8.85      inference('sup+', [status(thm)], ['41', '42'])).
% 8.64/8.85  thf('67', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ X1 @ X0)
% 8.64/8.85           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 8.64/8.85      inference('simplify', [status(thm)], ['53'])).
% 8.64/8.85  thf('68', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 8.64/8.85           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X0)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['66', '67'])).
% 8.64/8.85  thf('69', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 8.64/8.85           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.64/8.85      inference('sup+', [status(thm)], ['41', '42'])).
% 8.64/8.85  thf('70', plain,
% 8.64/8.85      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 8.64/8.85           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ (k1_tarski @ X13)))),
% 8.64/8.85      inference('cnf', [status(esa)], [t46_enumset1])).
% 8.64/8.85  thf('71', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X0 @ X0))),
% 8.64/8.85      inference('demod', [status(thm)], ['68', '69', '70'])).
% 8.64/8.85  thf('72', plain,
% 8.64/8.85      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 8.64/8.85           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 8.64/8.85      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.64/8.85  thf('73', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X0 @ X0))),
% 8.64/8.85      inference('sup+', [status(thm)], ['71', '72'])).
% 8.64/8.85  thf('74', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 8.64/8.85           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.64/8.85      inference('sup+', [status(thm)], ['41', '42'])).
% 8.64/8.85  thf('75', plain,
% 8.64/8.85      (![X1 : $i, X3 : $i, X5 : $i]:
% 8.64/8.85         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 8.64/8.85          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 8.64/8.85          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 8.64/8.85          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 8.64/8.85      inference('cnf', [status(esa)], [d3_xboole_0])).
% 8.64/8.85  thf('76', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 8.64/8.85          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 8.64/8.85          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 8.64/8.85      inference('eq_fact', [status(thm)], ['75'])).
% 8.64/8.85  thf('77', plain,
% 8.64/8.85      (![X1 : $i, X3 : $i, X5 : $i]:
% 8.64/8.85         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 8.64/8.85          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 8.64/8.85          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 8.64/8.85      inference('cnf', [status(esa)], [d3_xboole_0])).
% 8.64/8.85  thf('78', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 8.64/8.85          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 8.64/8.85          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 8.64/8.85          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 8.64/8.85      inference('sup-', [status(thm)], ['76', '77'])).
% 8.64/8.85  thf('79', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 8.64/8.85          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 8.64/8.85          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 8.64/8.85      inference('simplify', [status(thm)], ['78'])).
% 8.64/8.85  thf('80', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 8.64/8.85          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 8.64/8.85          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 8.64/8.85      inference('eq_fact', [status(thm)], ['75'])).
% 8.64/8.85  thf('81', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 8.64/8.85          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 8.64/8.85      inference('clc', [status(thm)], ['79', '80'])).
% 8.64/8.85  thf('82', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X3 : $i]:
% 8.64/8.85         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 8.64/8.85      inference('simplify', [status(thm)], ['49'])).
% 8.64/8.85  thf('83', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 8.64/8.85          | (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 8.64/8.85      inference('sup-', [status(thm)], ['81', '82'])).
% 8.64/8.85  thf('84', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 8.64/8.85          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 8.64/8.85      inference('clc', [status(thm)], ['79', '80'])).
% 8.64/8.85  thf('85', plain,
% 8.64/8.85      (![X1 : $i, X3 : $i, X5 : $i]:
% 8.64/8.85         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 8.64/8.85          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 8.64/8.85          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 8.64/8.85      inference('cnf', [status(esa)], [d3_xboole_0])).
% 8.64/8.85  thf('86', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 8.64/8.85          | ~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 8.64/8.85          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 8.64/8.85      inference('sup-', [status(thm)], ['84', '85'])).
% 8.64/8.85  thf('87', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 8.64/8.85          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 8.64/8.85      inference('simplify', [status(thm)], ['86'])).
% 8.64/8.85  thf('88', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         (((k2_xboole_0 @ X1 @ X0)
% 8.64/8.85            = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 8.64/8.85          | ((k2_xboole_0 @ X1 @ X0)
% 8.64/8.85              = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 8.64/8.85      inference('sup-', [status(thm)], ['83', '87'])).
% 8.64/8.85  thf('89', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ X1 @ X0)
% 8.64/8.85           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.64/8.85      inference('simplify', [status(thm)], ['88'])).
% 8.64/8.85  thf('90', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['74', '89'])).
% 8.64/8.85  thf('91', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 8.64/8.85           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.64/8.85      inference('sup+', [status(thm)], ['41', '42'])).
% 8.64/8.85  thf('92', plain,
% 8.64/8.85      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 8.64/8.85      inference('cnf', [status(esa)], [t44_enumset1])).
% 8.64/8.85  thf('93', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X2 @ X1 @ X0))),
% 8.64/8.85      inference('demod', [status(thm)], ['90', '91', '92'])).
% 8.64/8.85  thf('94', plain,
% 8.64/8.85      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 8.64/8.85      inference('cnf', [status(esa)], [t44_enumset1])).
% 8.64/8.85  thf('95', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 8.64/8.85              (k2_enumset1 @ X0 @ X2 @ X1 @ X0)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['93', '94'])).
% 8.64/8.85  thf('96', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 8.64/8.85              (k2_enumset1 @ X0 @ X1 @ X0 @ X0)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['73', '95'])).
% 8.64/8.85  thf('97', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 8.64/8.85      inference('demod', [status(thm)], ['55', '56', '57'])).
% 8.64/8.85  thf('98', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X2 @ X1 @ X0))),
% 8.64/8.85      inference('demod', [status(thm)], ['90', '91', '92'])).
% 8.64/8.85  thf('99', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i]:
% 8.64/8.85         ((k2_tarski @ X1 @ X0) = (k2_enumset1 @ X0 @ X1 @ X0 @ X0))),
% 8.64/8.85      inference('sup+', [status(thm)], ['97', '98'])).
% 8.64/8.85  thf('100', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 8.64/8.85      inference('demod', [status(thm)], ['96', '99'])).
% 8.64/8.85  thf('101', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k1_enumset1 @ X2 @ X1 @ X0)
% 8.64/8.85           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 8.64/8.85      inference('sup+', [status(thm)], ['62', '63'])).
% 8.64/8.85  thf('102', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.64/8.85      inference('demod', [status(thm)], ['100', '101'])).
% 8.64/8.85  thf('103', plain,
% 8.64/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.64/8.85         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 8.64/8.85      inference('sup+', [status(thm)], ['65', '102'])).
% 8.64/8.85  thf('104', plain,
% 8.64/8.85      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 8.64/8.85         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 8.64/8.85      inference('demod', [status(thm)], ['0', '103'])).
% 8.64/8.85  thf('105', plain, ($false), inference('simplify', [status(thm)], ['104'])).
% 8.64/8.85  
% 8.64/8.85  % SZS output end Refutation
% 8.64/8.85  
% 8.64/8.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
