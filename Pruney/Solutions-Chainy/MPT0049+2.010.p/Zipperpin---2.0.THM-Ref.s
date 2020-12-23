%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K6TnubyAHt

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:04 EST 2020

% Result     : Theorem 51.10s
% Output     : Refutation 51.10s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 391 expanded)
%              Number of leaves         :   15 ( 133 expanded)
%              Depth                    :   17
%              Number of atoms          : 1006 (3404 expanded)
%              Number of equality atoms :   94 ( 341 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t42_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','42'])).

thf('44',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('68',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['65','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['59','75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['44','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['59','75','76'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['78','79','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','87'])).

thf('89',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','88'])).

thf('90',plain,(
    $false ),
    inference(simplify,[status(thm)],['89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K6TnubyAHt
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:49:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 51.10/51.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 51.10/51.32  % Solved by: fo/fo7.sh
% 51.10/51.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 51.10/51.32  % done 15967 iterations in 50.868s
% 51.10/51.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 51.10/51.32  % SZS output start Refutation
% 51.10/51.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 51.10/51.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 51.10/51.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 51.10/51.32  thf(sk_A_type, type, sk_A: $i).
% 51.10/51.32  thf(sk_C_type, type, sk_C: $i).
% 51.10/51.32  thf(sk_B_type, type, sk_B: $i).
% 51.10/51.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 51.10/51.32  thf(t42_xboole_1, conjecture,
% 51.10/51.32    (![A:$i,B:$i,C:$i]:
% 51.10/51.32     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 51.10/51.32       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 51.10/51.32  thf(zf_stmt_0, negated_conjecture,
% 51.10/51.32    (~( ![A:$i,B:$i,C:$i]:
% 51.10/51.32        ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 51.10/51.32          ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )),
% 51.10/51.32    inference('cnf.neg', [status(esa)], [t42_xboole_1])).
% 51.10/51.32  thf('0', plain,
% 51.10/51.32      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 51.10/51.32         != (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 51.10/51.32             (k4_xboole_0 @ sk_B @ sk_C)))),
% 51.10/51.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.10/51.32  thf(t36_xboole_1, axiom,
% 51.10/51.32    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 51.10/51.32  thf('1', plain,
% 51.10/51.32      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 51.10/51.32      inference('cnf', [status(esa)], [t36_xboole_1])).
% 51.10/51.32  thf(l32_xboole_1, axiom,
% 51.10/51.32    (![A:$i,B:$i]:
% 51.10/51.32     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 51.10/51.32  thf('2', plain,
% 51.10/51.32      (![X2 : $i, X4 : $i]:
% 51.10/51.32         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 51.10/51.32      inference('cnf', [status(esa)], [l32_xboole_1])).
% 51.10/51.32  thf('3', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 51.10/51.32      inference('sup-', [status(thm)], ['1', '2'])).
% 51.10/51.32  thf(t41_xboole_1, axiom,
% 51.10/51.32    (![A:$i,B:$i,C:$i]:
% 51.10/51.32     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 51.10/51.32       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 51.10/51.32  thf('4', plain,
% 51.10/51.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 51.10/51.32           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 51.10/51.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.10/51.32  thf('5', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 51.10/51.32      inference('demod', [status(thm)], ['3', '4'])).
% 51.10/51.32  thf('6', plain,
% 51.10/51.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 51.10/51.32           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 51.10/51.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.10/51.32  thf('7', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k1_xboole_0)
% 51.10/51.32           = (k4_xboole_0 @ X1 @ 
% 51.10/51.32              (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))))),
% 51.10/51.32      inference('sup+', [status(thm)], ['5', '6'])).
% 51.10/51.32  thf(t39_xboole_1, axiom,
% 51.10/51.32    (![A:$i,B:$i]:
% 51.10/51.32     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 51.10/51.32  thf('8', plain,
% 51.10/51.32      (![X9 : $i, X10 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 51.10/51.32           = (k2_xboole_0 @ X9 @ X10))),
% 51.10/51.32      inference('cnf', [status(esa)], [t39_xboole_1])).
% 51.10/51.32  thf('9', plain,
% 51.10/51.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 51.10/51.32           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 51.10/51.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.10/51.32  thf('10', plain,
% 51.10/51.32      (![X2 : $i, X3 : $i]:
% 51.10/51.32         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 51.10/51.32      inference('cnf', [status(esa)], [l32_xboole_1])).
% 51.10/51.32  thf('11', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 51.10/51.32          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 51.10/51.32      inference('sup-', [status(thm)], ['9', '10'])).
% 51.10/51.32  thf('12', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 51.10/51.32          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 51.10/51.32      inference('sup-', [status(thm)], ['8', '11'])).
% 51.10/51.32  thf('13', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         (((k1_xboole_0) != (k1_xboole_0))
% 51.10/51.32          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 51.10/51.32             (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)))),
% 51.10/51.32      inference('sup-', [status(thm)], ['7', '12'])).
% 51.10/51.32  thf('14', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 51.10/51.32          (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 51.10/51.32      inference('simplify', [status(thm)], ['13'])).
% 51.10/51.32  thf(t12_xboole_1, axiom,
% 51.10/51.32    (![A:$i,B:$i]:
% 51.10/51.32     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 51.10/51.32  thf('15', plain,
% 51.10/51.32      (![X5 : $i, X6 : $i]:
% 51.10/51.32         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 51.10/51.32      inference('cnf', [status(esa)], [t12_xboole_1])).
% 51.10/51.32  thf('16', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 51.10/51.32           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))
% 51.10/51.32           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 51.10/51.32      inference('sup-', [status(thm)], ['14', '15'])).
% 51.10/51.32  thf('17', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 51.10/51.32      inference('demod', [status(thm)], ['3', '4'])).
% 51.10/51.32  thf('18', plain,
% 51.10/51.32      (![X2 : $i, X3 : $i]:
% 51.10/51.32         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 51.10/51.32      inference('cnf', [status(esa)], [l32_xboole_1])).
% 51.10/51.32  thf('19', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         (((k1_xboole_0) != (k1_xboole_0))
% 51.10/51.32          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.10/51.32      inference('sup-', [status(thm)], ['17', '18'])).
% 51.10/51.32  thf('20', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 51.10/51.32      inference('simplify', [status(thm)], ['19'])).
% 51.10/51.32  thf('21', plain,
% 51.10/51.32      (![X5 : $i, X6 : $i]:
% 51.10/51.32         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 51.10/51.32      inference('cnf', [status(esa)], [t12_xboole_1])).
% 51.10/51.32  thf('22', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 51.10/51.32           = (k2_xboole_0 @ X1 @ X0))),
% 51.10/51.32      inference('sup-', [status(thm)], ['20', '21'])).
% 51.10/51.32  thf(t40_xboole_1, axiom,
% 51.10/51.32    (![A:$i,B:$i]:
% 51.10/51.32     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 51.10/51.32  thf('23', plain,
% 51.10/51.32      (![X11 : $i, X12 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12)
% 51.10/51.32           = (k4_xboole_0 @ X11 @ X12))),
% 51.10/51.32      inference('cnf', [status(esa)], [t40_xboole_1])).
% 51.10/51.32  thf('24', plain,
% 51.10/51.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 51.10/51.32           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 51.10/51.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.10/51.32  thf('25', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 51.10/51.32           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 51.10/51.32      inference('sup+', [status(thm)], ['23', '24'])).
% 51.10/51.32  thf('26', plain,
% 51.10/51.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 51.10/51.32           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 51.10/51.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.10/51.32  thf('27', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 51.10/51.32           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 51.10/51.32      inference('demod', [status(thm)], ['25', '26'])).
% 51.10/51.32  thf('28', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 51.10/51.32           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 51.10/51.32      inference('sup+', [status(thm)], ['22', '27'])).
% 51.10/51.32  thf('29', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 51.10/51.32           = (k2_xboole_0 @ X1 @ X0))),
% 51.10/51.32      inference('sup-', [status(thm)], ['20', '21'])).
% 51.10/51.32  thf('30', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 51.10/51.32           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 51.10/51.32      inference('demod', [status(thm)], ['28', '29'])).
% 51.10/51.32  thf('31', plain,
% 51.10/51.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 51.10/51.32           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 51.10/51.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.10/51.32  thf('32', plain,
% 51.10/51.32      (![X9 : $i, X10 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 51.10/51.32           = (k2_xboole_0 @ X9 @ X10))),
% 51.10/51.32      inference('cnf', [status(esa)], [t39_xboole_1])).
% 51.10/51.32  thf('33', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 51.10/51.32           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 51.10/51.32      inference('sup+', [status(thm)], ['31', '32'])).
% 51.10/51.32  thf('34', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 51.10/51.32           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1)))),
% 51.10/51.32      inference('sup+', [status(thm)], ['30', '33'])).
% 51.10/51.32  thf('35', plain,
% 51.10/51.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 51.10/51.32           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 51.10/51.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.10/51.32  thf('36', plain,
% 51.10/51.32      (![X11 : $i, X12 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12)
% 51.10/51.32           = (k4_xboole_0 @ X11 @ X12))),
% 51.10/51.32      inference('cnf', [status(esa)], [t40_xboole_1])).
% 51.10/51.32  thf('37', plain,
% 51.10/51.32      (![X9 : $i, X10 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 51.10/51.32           = (k2_xboole_0 @ X9 @ X10))),
% 51.10/51.32      inference('cnf', [status(esa)], [t39_xboole_1])).
% 51.10/51.32  thf('38', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 51.10/51.32           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.10/51.32      inference('sup+', [status(thm)], ['36', '37'])).
% 51.10/51.32  thf('39', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 51.10/51.32           = (k2_xboole_0 @ X1 @ X0))),
% 51.10/51.32      inference('sup-', [status(thm)], ['20', '21'])).
% 51.10/51.32  thf('40', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 51.10/51.32           = (k2_xboole_0 @ X1 @ X0))),
% 51.10/51.32      inference('demod', [status(thm)], ['38', '39'])).
% 51.10/51.32  thf('41', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 51.10/51.32           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 51.10/51.32      inference('sup+', [status(thm)], ['35', '40'])).
% 51.10/51.32  thf('42', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 51.10/51.32           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1)))),
% 51.10/51.32      inference('demod', [status(thm)], ['34', '41'])).
% 51.10/51.32  thf('43', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 51.10/51.32           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 51.10/51.32      inference('demod', [status(thm)], ['16', '42'])).
% 51.10/51.32  thf('44', plain,
% 51.10/51.32      (![X9 : $i, X10 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 51.10/51.32           = (k2_xboole_0 @ X9 @ X10))),
% 51.10/51.32      inference('cnf', [status(esa)], [t39_xboole_1])).
% 51.10/51.32  thf(commutativity_k2_xboole_0, axiom,
% 51.10/51.32    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 51.10/51.32  thf('45', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.10/51.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.10/51.32  thf('46', plain,
% 51.10/51.32      (![X11 : $i, X12 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12)
% 51.10/51.32           = (k4_xboole_0 @ X11 @ X12))),
% 51.10/51.32      inference('cnf', [status(esa)], [t40_xboole_1])).
% 51.10/51.32  thf('47', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 51.10/51.32           = (k4_xboole_0 @ X0 @ X1))),
% 51.10/51.32      inference('sup+', [status(thm)], ['45', '46'])).
% 51.10/51.32  thf('48', plain,
% 51.10/51.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 51.10/51.32           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 51.10/51.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.10/51.32  thf('49', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 51.10/51.32           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 51.10/51.32      inference('sup+', [status(thm)], ['47', '48'])).
% 51.10/51.32  thf('50', plain,
% 51.10/51.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 51.10/51.32           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 51.10/51.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.10/51.32  thf('51', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 51.10/51.32           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 51.10/51.32      inference('demod', [status(thm)], ['49', '50'])).
% 51.10/51.32  thf('52', plain,
% 51.10/51.32      (![X9 : $i, X10 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 51.10/51.32           = (k2_xboole_0 @ X9 @ X10))),
% 51.10/51.32      inference('cnf', [status(esa)], [t39_xboole_1])).
% 51.10/51.32  thf('53', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 51.10/51.32           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 51.10/51.32           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X2)))),
% 51.10/51.32      inference('sup+', [status(thm)], ['51', '52'])).
% 51.10/51.32  thf('54', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 51.10/51.32           = (k2_xboole_0 @ X1 @ X0))),
% 51.10/51.32      inference('demod', [status(thm)], ['38', '39'])).
% 51.10/51.32  thf('55', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 51.10/51.32           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X2)))),
% 51.10/51.32      inference('demod', [status(thm)], ['53', '54'])).
% 51.10/51.32  thf('56', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.10/51.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.10/51.32  thf('57', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 51.10/51.32           = (k2_xboole_0 @ X1 @ X0))),
% 51.10/51.32      inference('sup-', [status(thm)], ['20', '21'])).
% 51.10/51.32  thf('58', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 51.10/51.32           = (k2_xboole_0 @ X0 @ X1))),
% 51.10/51.32      inference('sup+', [status(thm)], ['56', '57'])).
% 51.10/51.32  thf('59', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 51.10/51.32           (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 51.10/51.32           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 51.10/51.32      inference('sup+', [status(thm)], ['55', '58'])).
% 51.10/51.32  thf('60', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.10/51.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.10/51.32  thf('61', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.10/51.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.10/51.32  thf('62', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 51.10/51.32      inference('demod', [status(thm)], ['3', '4'])).
% 51.10/51.32  thf('63', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 51.10/51.32      inference('sup+', [status(thm)], ['61', '62'])).
% 51.10/51.32  thf('64', plain,
% 51.10/51.32      (![X9 : $i, X10 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 51.10/51.32           = (k2_xboole_0 @ X9 @ X10))),
% 51.10/51.32      inference('cnf', [status(esa)], [t39_xboole_1])).
% 51.10/51.32  thf('65', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 51.10/51.32           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 51.10/51.32      inference('sup+', [status(thm)], ['63', '64'])).
% 51.10/51.32  thf('66', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 51.10/51.32      inference('demod', [status(thm)], ['3', '4'])).
% 51.10/51.32  thf('67', plain,
% 51.10/51.32      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 51.10/51.32      inference('cnf', [status(esa)], [t36_xboole_1])).
% 51.10/51.32  thf('68', plain,
% 51.10/51.32      (![X5 : $i, X6 : $i]:
% 51.10/51.32         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 51.10/51.32      inference('cnf', [status(esa)], [t12_xboole_1])).
% 51.10/51.32  thf('69', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 51.10/51.32      inference('sup-', [status(thm)], ['67', '68'])).
% 51.10/51.32  thf('70', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.10/51.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.10/51.32  thf('71', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 51.10/51.32      inference('demod', [status(thm)], ['69', '70'])).
% 51.10/51.32  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 51.10/51.32      inference('sup+', [status(thm)], ['66', '71'])).
% 51.10/51.32  thf('73', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.10/51.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.10/51.32  thf('74', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X0 @ X1)
% 51.10/51.32           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 51.10/51.32      inference('demod', [status(thm)], ['65', '72', '73'])).
% 51.10/51.32  thf('75', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X0 @ X1)
% 51.10/51.32           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.10/51.32      inference('sup+', [status(thm)], ['60', '74'])).
% 51.10/51.32  thf('76', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 51.10/51.32           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X2)))),
% 51.10/51.32      inference('demod', [status(thm)], ['53', '54'])).
% 51.10/51.32  thf('77', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 51.10/51.32           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 51.10/51.32      inference('demod', [status(thm)], ['59', '75', '76'])).
% 51.10/51.32  thf('78', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)
% 51.10/51.32           = (k2_xboole_0 @ X1 @ 
% 51.10/51.32              (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)))))),
% 51.10/51.32      inference('sup+', [status(thm)], ['44', '77'])).
% 51.10/51.32  thf('79', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 51.10/51.32           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 51.10/51.32      inference('demod', [status(thm)], ['59', '75', '76'])).
% 51.10/51.32  thf('80', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.10/51.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.10/51.32  thf('81', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 51.10/51.32           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 51.10/51.32      inference('sup+', [status(thm)], ['31', '32'])).
% 51.10/51.32  thf('82', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 51.10/51.32           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0)))),
% 51.10/51.32      inference('sup+', [status(thm)], ['80', '81'])).
% 51.10/51.32  thf('83', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X0))
% 51.10/51.32           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))))),
% 51.10/51.32      inference('demod', [status(thm)], ['78', '79', '82'])).
% 51.10/51.32  thf('84', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 51.10/51.32           = (k4_xboole_0 @ X0 @ X1))),
% 51.10/51.32      inference('sup+', [status(thm)], ['45', '46'])).
% 51.10/51.32  thf('85', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X2)
% 51.10/51.32           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2)) @ X2))),
% 51.10/51.32      inference('sup+', [status(thm)], ['83', '84'])).
% 51.10/51.32  thf('86', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 51.10/51.32           = (k4_xboole_0 @ X0 @ X1))),
% 51.10/51.32      inference('sup+', [status(thm)], ['45', '46'])).
% 51.10/51.32  thf('87', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 51.10/51.32           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2)) @ X2))),
% 51.10/51.32      inference('demod', [status(thm)], ['85', '86'])).
% 51.10/51.32  thf('88', plain,
% 51.10/51.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.10/51.32         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)
% 51.10/51.32           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 51.10/51.32      inference('sup+', [status(thm)], ['43', '87'])).
% 51.10/51.32  thf('89', plain,
% 51.10/51.32      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 51.10/51.32         != (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 51.10/51.32      inference('demod', [status(thm)], ['0', '88'])).
% 51.10/51.32  thf('90', plain, ($false), inference('simplify', [status(thm)], ['89'])).
% 51.10/51.32  
% 51.10/51.32  % SZS output end Refutation
% 51.10/51.32  
% 51.10/51.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
