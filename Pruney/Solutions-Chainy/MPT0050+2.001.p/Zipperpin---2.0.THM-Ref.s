%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5ed6ksUdqw

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:04 EST 2020

% Result     : Theorem 2.42s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 179 expanded)
%              Number of leaves         :   14 (  67 expanded)
%              Depth                    :   16
%              Number of atoms          :  879 (1543 expanded)
%              Number of equality atoms :   79 ( 144 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t43_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
       => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t43_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ X0 )
      = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['29','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['25','28','43','44'])).

thf('46',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['11','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('49',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k2_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_C @ sk_B ) ) )
    = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('68',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('69',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('70',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('76',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('78',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','66','67','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('80',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['0','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5ed6ksUdqw
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:48:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.42/2.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.42/2.61  % Solved by: fo/fo7.sh
% 2.42/2.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.42/2.61  % done 1741 iterations in 2.141s
% 2.42/2.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.42/2.61  % SZS output start Refutation
% 2.42/2.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.42/2.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.42/2.61  thf(sk_A_type, type, sk_A: $i).
% 2.42/2.61  thf(sk_C_type, type, sk_C: $i).
% 2.42/2.61  thf(sk_B_type, type, sk_B: $i).
% 2.42/2.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.42/2.61  thf(t43_xboole_1, conjecture,
% 2.42/2.61    (![A:$i,B:$i,C:$i]:
% 2.42/2.61     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 2.42/2.61       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 2.42/2.61  thf(zf_stmt_0, negated_conjecture,
% 2.42/2.61    (~( ![A:$i,B:$i,C:$i]:
% 2.42/2.61        ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 2.42/2.61          ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )),
% 2.42/2.61    inference('cnf.neg', [status(esa)], [t43_xboole_1])).
% 2.42/2.61  thf('0', plain, (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 2.42/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.61  thf('1', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 2.42/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.61  thf(t12_xboole_1, axiom,
% 2.42/2.61    (![A:$i,B:$i]:
% 2.42/2.61     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.42/2.61  thf('2', plain,
% 2.42/2.61      (![X2 : $i, X3 : $i]:
% 2.42/2.61         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 2.42/2.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.42/2.61  thf('3', plain,
% 2.42/2.61      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 2.42/2.61         = (k2_xboole_0 @ sk_B @ sk_C))),
% 2.42/2.61      inference('sup-', [status(thm)], ['1', '2'])).
% 2.42/2.61  thf(commutativity_k2_xboole_0, axiom,
% 2.42/2.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.42/2.61  thf('4', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.42/2.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.42/2.61  thf('5', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.42/2.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.42/2.61  thf('6', plain,
% 2.42/2.61      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))
% 2.42/2.61         = (k2_xboole_0 @ sk_C @ sk_B))),
% 2.42/2.61      inference('demod', [status(thm)], ['3', '4', '5'])).
% 2.42/2.61  thf(t4_xboole_1, axiom,
% 2.42/2.61    (![A:$i,B:$i,C:$i]:
% 2.42/2.61     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 2.42/2.61       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.42/2.61  thf('7', plain,
% 2.42/2.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 2.42/2.61           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.42/2.61  thf('8', plain,
% 2.42/2.61      (![X0 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ X0)
% 2.42/2.61           = (k2_xboole_0 @ sk_A @ 
% 2.42/2.61              (k2_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ X0)))),
% 2.42/2.61      inference('sup+', [status(thm)], ['6', '7'])).
% 2.42/2.61  thf('9', plain,
% 2.42/2.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 2.42/2.61           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.42/2.61  thf('10', plain,
% 2.42/2.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 2.42/2.61           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.42/2.61  thf('11', plain,
% 2.42/2.61      (![X0 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ X0))
% 2.42/2.61           = (k2_xboole_0 @ sk_A @ 
% 2.42/2.61              (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ X0))))),
% 2.42/2.61      inference('demod', [status(thm)], ['8', '9', '10'])).
% 2.42/2.61  thf(t40_xboole_1, axiom,
% 2.42/2.61    (![A:$i,B:$i]:
% 2.42/2.61     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.42/2.61  thf('12', plain,
% 2.42/2.61      (![X6 : $i, X7 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 2.42/2.61           = (k4_xboole_0 @ X6 @ X7))),
% 2.42/2.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.42/2.61  thf(t36_xboole_1, axiom,
% 2.42/2.61    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.42/2.61  thf('13', plain,
% 2.42/2.61      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 2.42/2.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.42/2.61  thf('14', plain,
% 2.42/2.61      (![X2 : $i, X3 : $i]:
% 2.42/2.61         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 2.42/2.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.42/2.61  thf('15', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.42/2.61      inference('sup-', [status(thm)], ['13', '14'])).
% 2.42/2.61  thf('16', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.42/2.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.42/2.61  thf('17', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 2.42/2.61      inference('demod', [status(thm)], ['15', '16'])).
% 2.42/2.61  thf('18', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.42/2.61           = (k2_xboole_0 @ X1 @ X0))),
% 2.42/2.61      inference('sup+', [status(thm)], ['12', '17'])).
% 2.42/2.61  thf('19', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.42/2.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.42/2.61  thf('20', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 2.42/2.61           = (k2_xboole_0 @ X1 @ X0))),
% 2.42/2.61      inference('demod', [status(thm)], ['18', '19'])).
% 2.42/2.61  thf('21', plain,
% 2.42/2.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 2.42/2.61           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.42/2.61  thf('22', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 2.42/2.61           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 2.42/2.61              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)))),
% 2.42/2.61      inference('sup+', [status(thm)], ['20', '21'])).
% 2.42/2.61  thf('23', plain,
% 2.42/2.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 2.42/2.61           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.42/2.61  thf('24', plain,
% 2.42/2.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 2.42/2.61           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.42/2.61  thf('25', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 2.42/2.61           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 2.42/2.61              (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))))),
% 2.42/2.61      inference('demod', [status(thm)], ['22', '23', '24'])).
% 2.42/2.61  thf('26', plain,
% 2.42/2.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 2.42/2.61           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.42/2.61  thf('27', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.42/2.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.42/2.61  thf('28', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 2.42/2.61           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.42/2.61      inference('sup+', [status(thm)], ['26', '27'])).
% 2.42/2.61  thf('29', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.42/2.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.42/2.61  thf('30', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.42/2.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.42/2.61  thf('31', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.42/2.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.42/2.61  thf(t7_xboole_1, axiom,
% 2.42/2.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.42/2.61  thf('32', plain,
% 2.42/2.61      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 2.42/2.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.42/2.61  thf('33', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.42/2.61      inference('sup+', [status(thm)], ['31', '32'])).
% 2.42/2.61  thf('34', plain,
% 2.42/2.61      (![X2 : $i, X3 : $i]:
% 2.42/2.61         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 2.42/2.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.42/2.61  thf('35', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 2.42/2.61           = (k2_xboole_0 @ X1 @ X0))),
% 2.42/2.61      inference('sup-', [status(thm)], ['33', '34'])).
% 2.42/2.61  thf('36', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 2.42/2.61           = (k2_xboole_0 @ X0 @ X1))),
% 2.42/2.61      inference('sup+', [status(thm)], ['30', '35'])).
% 2.42/2.61  thf('37', plain,
% 2.42/2.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 2.42/2.61           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.42/2.61  thf('38', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 2.42/2.61           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)))),
% 2.42/2.61      inference('sup+', [status(thm)], ['36', '37'])).
% 2.42/2.61  thf('39', plain,
% 2.42/2.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 2.42/2.61           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.42/2.61  thf('40', plain,
% 2.42/2.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 2.42/2.61           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.42/2.61  thf('41', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 2.42/2.61           = (k2_xboole_0 @ X0 @ X1))),
% 2.42/2.61      inference('sup+', [status(thm)], ['30', '35'])).
% 2.42/2.61  thf('42', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 2.42/2.61           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X0))),
% 2.42/2.61      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 2.42/2.61  thf('43', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 2.42/2.61           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 2.42/2.61      inference('sup+', [status(thm)], ['29', '42'])).
% 2.42/2.61  thf('44', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.42/2.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.42/2.61  thf('45', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 2.42/2.61           = (k2_xboole_0 @ X1 @ 
% 2.42/2.61              (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))))),
% 2.42/2.61      inference('demod', [status(thm)], ['25', '28', '43', '44'])).
% 2.42/2.61  thf('46', plain,
% 2.42/2.61      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 2.42/2.61         = (k2_xboole_0 @ sk_C @ 
% 2.42/2.61            (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 2.42/2.61      inference('sup+', [status(thm)], ['11', '45'])).
% 2.42/2.61  thf('47', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.42/2.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.42/2.61  thf('48', plain,
% 2.42/2.61      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))
% 2.42/2.61         = (k2_xboole_0 @ sk_C @ sk_B))),
% 2.42/2.61      inference('demod', [status(thm)], ['3', '4', '5'])).
% 2.42/2.61  thf('49', plain,
% 2.42/2.61      (((k2_xboole_0 @ sk_C @ sk_B)
% 2.42/2.61         = (k2_xboole_0 @ sk_C @ 
% 2.42/2.61            (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 2.42/2.61      inference('demod', [status(thm)], ['46', '47', '48'])).
% 2.42/2.61  thf('50', plain,
% 2.42/2.61      (![X6 : $i, X7 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 2.42/2.61           = (k4_xboole_0 @ X6 @ X7))),
% 2.42/2.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.42/2.61  thf(t42_xboole_1, axiom,
% 2.42/2.61    (![A:$i,B:$i,C:$i]:
% 2.42/2.61     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 2.42/2.61       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 2.42/2.61  thf('51', plain,
% 2.42/2.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X10) @ X9)
% 2.42/2.61           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X10 @ X9)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t42_xboole_1])).
% 2.42/2.61  thf('52', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X0)
% 2.42/2.61           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0)))),
% 2.42/2.61      inference('sup+', [status(thm)], ['50', '51'])).
% 2.42/2.61  thf('53', plain,
% 2.42/2.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X10) @ X9)
% 2.42/2.61           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X10 @ X9)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t42_xboole_1])).
% 2.42/2.61  thf('54', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X0)
% 2.42/2.61           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X0))),
% 2.42/2.61      inference('demod', [status(thm)], ['52', '53'])).
% 2.42/2.61  thf('55', plain,
% 2.42/2.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 2.42/2.61           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.42/2.61  thf('56', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)) @ X0)
% 2.42/2.61           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X0))),
% 2.42/2.61      inference('demod', [status(thm)], ['54', '55'])).
% 2.42/2.61  thf('57', plain,
% 2.42/2.61      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_B)
% 2.42/2.61         = (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 2.42/2.61            sk_B))),
% 2.42/2.61      inference('sup+', [status(thm)], ['49', '56'])).
% 2.42/2.61  thf('58', plain,
% 2.42/2.61      (![X6 : $i, X7 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 2.42/2.61           = (k4_xboole_0 @ X6 @ X7))),
% 2.42/2.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.42/2.61  thf('59', plain,
% 2.42/2.61      (((k4_xboole_0 @ sk_C @ sk_B)
% 2.42/2.61         = (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 2.42/2.61            sk_B))),
% 2.42/2.61      inference('demod', [status(thm)], ['57', '58'])).
% 2.42/2.61  thf('60', plain,
% 2.42/2.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 2.42/2.61           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.42/2.61  thf('61', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 2.42/2.61      inference('demod', [status(thm)], ['15', '16'])).
% 2.42/2.61  thf('62', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ X2 @ 
% 2.42/2.61           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))
% 2.42/2.61           = (k2_xboole_0 @ X2 @ X1))),
% 2.42/2.61      inference('sup+', [status(thm)], ['60', '61'])).
% 2.42/2.61  thf('63', plain,
% 2.42/2.61      (((k2_xboole_0 @ sk_C @ 
% 2.42/2.61         (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 2.42/2.61          (k4_xboole_0 @ sk_C @ sk_B)))
% 2.42/2.61         = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 2.42/2.61      inference('sup+', [status(thm)], ['59', '62'])).
% 2.42/2.61  thf('64', plain,
% 2.42/2.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X10) @ X9)
% 2.42/2.61           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X10 @ X9)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t42_xboole_1])).
% 2.42/2.61  thf('65', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.42/2.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.42/2.61  thf('66', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))
% 2.42/2.61           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 2.42/2.61      inference('sup+', [status(thm)], ['64', '65'])).
% 2.42/2.61  thf('67', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.42/2.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.42/2.61  thf('68', plain,
% 2.42/2.61      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))
% 2.42/2.61         = (k2_xboole_0 @ sk_C @ sk_B))),
% 2.42/2.61      inference('demod', [status(thm)], ['3', '4', '5'])).
% 2.42/2.61  thf('69', plain,
% 2.42/2.61      (![X6 : $i, X7 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 2.42/2.61           = (k4_xboole_0 @ X6 @ X7))),
% 2.42/2.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.42/2.61  thf('70', plain,
% 2.42/2.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X10) @ X9)
% 2.42/2.61           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X10 @ X9)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t42_xboole_1])).
% 2.42/2.61  thf('71', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)
% 2.42/2.61           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 2.42/2.61      inference('sup+', [status(thm)], ['69', '70'])).
% 2.42/2.61  thf('72', plain,
% 2.42/2.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X10) @ X9)
% 2.42/2.61           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X10 @ X9)))),
% 2.42/2.61      inference('cnf', [status(esa)], [t42_xboole_1])).
% 2.42/2.61  thf('73', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)
% 2.42/2.61           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 2.42/2.61      inference('demod', [status(thm)], ['71', '72'])).
% 2.42/2.61  thf('74', plain,
% 2.42/2.61      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_B)
% 2.42/2.61         = (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 2.42/2.61      inference('sup+', [status(thm)], ['68', '73'])).
% 2.42/2.61  thf('75', plain,
% 2.42/2.61      (![X6 : $i, X7 : $i]:
% 2.42/2.61         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 2.42/2.61           = (k4_xboole_0 @ X6 @ X7))),
% 2.42/2.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.42/2.61  thf('76', plain,
% 2.42/2.61      (((k4_xboole_0 @ sk_C @ sk_B)
% 2.42/2.61         = (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 2.42/2.61      inference('demod', [status(thm)], ['74', '75'])).
% 2.42/2.61  thf('77', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]:
% 2.42/2.61         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 2.42/2.61      inference('demod', [status(thm)], ['15', '16'])).
% 2.42/2.61  thf('78', plain,
% 2.42/2.61      (((sk_C) = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 2.42/2.61      inference('demod', [status(thm)], ['63', '66', '67', '76', '77'])).
% 2.42/2.61  thf('79', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.42/2.61      inference('sup+', [status(thm)], ['31', '32'])).
% 2.42/2.61  thf('80', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 2.42/2.61      inference('sup+', [status(thm)], ['78', '79'])).
% 2.42/2.61  thf('81', plain, ($false), inference('demod', [status(thm)], ['0', '80'])).
% 2.42/2.61  
% 2.42/2.61  % SZS output end Refutation
% 2.42/2.61  
% 2.42/2.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
