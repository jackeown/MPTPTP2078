%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sHQcYDoHSk

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:50 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  110 (1252 expanded)
%              Number of leaves         :   19 ( 426 expanded)
%              Depth                    :   33
%              Number of atoms          :  779 (8487 expanded)
%              Number of equality atoms :   93 (1156 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t89_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t89_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t82_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t82_xboole_1])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X15 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    ! [X15: $i] :
      ( ( X15 = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ X15 @ X15 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ o_0_0_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ o_0_0_xboole_0 @ X0 ) @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ o_0_0_xboole_0 @ ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ o_0_0_xboole_0 @ ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ o_0_0_xboole_0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ o_0_0_xboole_0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ o_0_0_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ o_0_0_xboole_0 @ X0 ) ) @ o_0_0_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 ) )
      = ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ o_0_0_xboole_0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['30','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','54'])).

thf('56',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('57',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf(t53_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ o_0_0_xboole_0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('69',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( o_0_0_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( o_0_0_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( o_0_0_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( o_0_0_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ o_0_0_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['66','67','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['58','81'])).

thf('83',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t82_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['0','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sHQcYDoHSk
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 443 iterations in 0.156s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.36/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(t89_xboole_1, conjecture,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (~( ![A:$i,B:$i]:
% 0.36/0.60        ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t89_xboole_1])).
% 0.36/0.60  thf('0', plain,
% 0.36/0.60      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.36/0.60          (k4_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t82_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ))).
% 0.36/0.60  thf('1', plain,
% 0.36/0.60      (![X18 : $i, X19 : $i]:
% 0.36/0.60         (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X19 @ X18))),
% 0.36/0.60      inference('cnf', [status(esa)], [t82_xboole_1])).
% 0.36/0.60  thf(t66_xboole_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.36/0.60       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.36/0.60  thf('2', plain,
% 0.36/0.60      (![X15 : $i]: (((X15) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X15 @ X15))),
% 0.36/0.60      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.36/0.60  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.36/0.60  thf('3', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.36/0.60  thf('4', plain,
% 0.36/0.60      (![X15 : $i]: (((X15) = (o_0_0_xboole_0)) | ~ (r1_xboole_0 @ X15 @ X15))),
% 0.36/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.60  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (o_0_0_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['1', '4'])).
% 0.36/0.60  thf(t52_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.36/0.60       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.36/0.60  thf('6', plain,
% 0.36/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 0.36/0.60           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X10)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.36/0.60  thf('7', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.60           = (k2_xboole_0 @ o_0_0_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.36/0.60  thf('8', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.36/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.36/0.60  thf(t51_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.36/0.60       ( A ) ))).
% 0.36/0.60  thf('9', plain,
% 0.36/0.60      (![X6 : $i, X7 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X7))
% 0.36/0.60           = (X6))),
% 0.36/0.60      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.36/0.60  thf('10', plain,
% 0.36/0.60      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.60  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (o_0_0_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['1', '4'])).
% 0.36/0.60  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ o_0_0_xboole_0) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.60  thf(t6_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.60  thf('13', plain,
% 0.36/0.60      (![X16 : $i, X17 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17))
% 0.36/0.60           = (k2_xboole_0 @ X16 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.36/0.60  thf('14', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ o_0_0_xboole_0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['12', '13'])).
% 0.36/0.60  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ o_0_0_xboole_0) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.60  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['14', '15'])).
% 0.36/0.60  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (o_0_0_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['1', '4'])).
% 0.36/0.60  thf(t41_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.60       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.60  thf('18', plain,
% 0.36/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ X5)
% 0.36/0.60           = (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.60  thf('19', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ o_0_0_xboole_0 @ X0)
% 0.36/0.60           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['17', '18'])).
% 0.36/0.60  thf('20', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ o_0_0_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['16', '19'])).
% 0.36/0.60  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (o_0_0_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['1', '4'])).
% 0.36/0.60  thf('22', plain,
% 0.36/0.60      (![X0 : $i]: ((k4_xboole_0 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0))),
% 0.36/0.60      inference('demod', [status(thm)], ['20', '21'])).
% 0.36/0.60  thf('23', plain,
% 0.36/0.60      (![X6 : $i, X7 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X7))
% 0.36/0.60           = (X6))),
% 0.36/0.60      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.36/0.60  thf('24', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ (k3_xboole_0 @ o_0_0_xboole_0 @ X0) @ o_0_0_xboole_0)
% 0.36/0.60           = (o_0_0_xboole_0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['22', '23'])).
% 0.36/0.60  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ o_0_0_xboole_0) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.60  thf('26', plain,
% 0.36/0.60      (![X0 : $i]: ((k3_xboole_0 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0))),
% 0.36/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.60  thf('27', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.60  thf('28', plain,
% 0.36/0.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['26', '27'])).
% 0.36/0.60  thf('29', plain,
% 0.36/0.60      (![X6 : $i, X7 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X7))
% 0.36/0.60           = (X6))),
% 0.36/0.60      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.36/0.60  thf('30', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ o_0_0_xboole_0 @ (k4_xboole_0 @ X0 @ o_0_0_xboole_0))
% 0.36/0.60           = (X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['28', '29'])).
% 0.36/0.60  thf('31', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ o_0_0_xboole_0 @ (k4_xboole_0 @ X0 @ o_0_0_xboole_0))
% 0.36/0.60           = (X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['28', '29'])).
% 0.36/0.60  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (o_0_0_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['1', '4'])).
% 0.36/0.60  thf('33', plain,
% 0.36/0.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['26', '27'])).
% 0.36/0.60  thf('34', plain,
% 0.36/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 0.36/0.60           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X10)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.36/0.60  thf('35', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ o_0_0_xboole_0))
% 0.36/0.60           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ o_0_0_xboole_0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['33', '34'])).
% 0.36/0.60  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ o_0_0_xboole_0) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.60  thf('37', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ o_0_0_xboole_0))
% 0.36/0.60           = (k4_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('demod', [status(thm)], ['35', '36'])).
% 0.36/0.60  thf('38', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((o_0_0_xboole_0)
% 0.36/0.60           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ o_0_0_xboole_0) @ X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['32', '37'])).
% 0.36/0.60  thf('39', plain,
% 0.36/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ X5)
% 0.36/0.60           = (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.60  thf('40', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((o_0_0_xboole_0)
% 0.36/0.60           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ o_0_0_xboole_0 @ X0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['38', '39'])).
% 0.36/0.60  thf('41', plain,
% 0.36/0.60      (![X6 : $i, X7 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X7))
% 0.36/0.60           = (X6))),
% 0.36/0.60      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.36/0.60  thf('42', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ 
% 0.36/0.60           (k3_xboole_0 @ X0 @ (k2_xboole_0 @ o_0_0_xboole_0 @ X0)) @ 
% 0.36/0.60           o_0_0_xboole_0) = (X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.60  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ o_0_0_xboole_0) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.60  thf('44', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ o_0_0_xboole_0 @ X0)) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['42', '43'])).
% 0.36/0.60  thf('45', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ o_0_0_xboole_0) @ X0)
% 0.36/0.60           = (k4_xboole_0 @ X0 @ o_0_0_xboole_0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['31', '44'])).
% 0.36/0.60  thf('46', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.60  thf('47', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ o_0_0_xboole_0))
% 0.36/0.60           = (k4_xboole_0 @ X0 @ o_0_0_xboole_0))),
% 0.36/0.60      inference('demod', [status(thm)], ['45', '46'])).
% 0.36/0.60  thf('48', plain,
% 0.36/0.60      (![X6 : $i, X7 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X7))
% 0.36/0.60           = (X6))),
% 0.36/0.60      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.36/0.60  thf('49', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ o_0_0_xboole_0) @ 
% 0.36/0.60           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ o_0_0_xboole_0))) = (
% 0.36/0.60           X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['47', '48'])).
% 0.36/0.60  thf('50', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ o_0_0_xboole_0))
% 0.36/0.60           = (k4_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('demod', [status(thm)], ['35', '36'])).
% 0.36/0.60  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (o_0_0_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['1', '4'])).
% 0.36/0.60  thf('52', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ o_0_0_xboole_0) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.60  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ o_0_0_xboole_0) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.36/0.60  thf('54', plain, (![X0 : $i]: ((k2_xboole_0 @ o_0_0_xboole_0 @ X0) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['30', '53'])).
% 0.36/0.60  thf('55', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.60           = (k3_xboole_0 @ X1 @ X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['7', '54'])).
% 0.36/0.60  thf('56', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.36/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.36/0.60  thf('57', plain,
% 0.36/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 0.36/0.60           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X10)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.36/0.60  thf('58', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.60           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['56', '57'])).
% 0.36/0.60  thf('59', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.60           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['56', '57'])).
% 0.36/0.60  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ o_0_0_xboole_0) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.36/0.60  thf(t53_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.36/0.60       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.36/0.60  thf('61', plain,
% 0.36/0.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13))
% 0.36/0.60           = (k3_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ 
% 0.36/0.60              (k4_xboole_0 @ X11 @ X13)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t53_xboole_1])).
% 0.36/0.60  thf('62', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ o_0_0_xboole_0))
% 0.36/0.60           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['60', '61'])).
% 0.36/0.60  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ o_0_0_xboole_0) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.60  thf('64', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.60  thf('65', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X0 @ X1)
% 0.36/0.60           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.60      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.36/0.60  thf('66', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.60           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['59', '65'])).
% 0.36/0.60  thf('67', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.60           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['56', '57'])).
% 0.36/0.60  thf('68', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X0 @ X1)
% 0.36/0.60           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.60      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.36/0.60  thf('69', plain,
% 0.36/0.60      (![X6 : $i, X7 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X7))
% 0.36/0.60           = (X6))),
% 0.36/0.60      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.36/0.60  thf('70', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ o_0_0_xboole_0 @ X0)
% 0.36/0.60           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['17', '18'])).
% 0.36/0.60  thf('71', plain,
% 0.36/0.60      (![X0 : $i]: ((k4_xboole_0 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0))),
% 0.36/0.60      inference('demod', [status(thm)], ['20', '21'])).
% 0.36/0.60  thf('72', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((o_0_0_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['70', '71'])).
% 0.36/0.60  thf('73', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((o_0_0_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['69', '72'])).
% 0.36/0.60  thf('74', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((o_0_0_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.36/0.60      inference('sup+', [status(thm)], ['68', '73'])).
% 0.36/0.60  thf('75', plain,
% 0.36/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ X5)
% 0.36/0.60           = (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.60  thf('76', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((o_0_0_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.36/0.60      inference('demod', [status(thm)], ['74', '75'])).
% 0.36/0.60  thf('77', plain,
% 0.36/0.60      (![X6 : $i, X7 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X7))
% 0.36/0.60           = (X6))),
% 0.36/0.60      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.36/0.60  thf('78', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.36/0.60           o_0_0_xboole_0) = (X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['76', '77'])).
% 0.36/0.60  thf('79', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ o_0_0_xboole_0) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.60  thf('80', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['78', '79'])).
% 0.36/0.60  thf('81', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['66', '67', '80'])).
% 0.36/0.60  thf('82', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['58', '81'])).
% 0.36/0.60  thf('83', plain,
% 0.36/0.60      (![X18 : $i, X19 : $i]:
% 0.36/0.60         (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X19 @ X18))),
% 0.36/0.60      inference('cnf', [status(esa)], [t82_xboole_1])).
% 0.36/0.60  thf('84', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) @ X0)),
% 0.36/0.60      inference('sup+', [status(thm)], ['82', '83'])).
% 0.36/0.60  thf('85', plain,
% 0.36/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ X5)
% 0.36/0.60           = (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.60  thf('86', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['14', '15'])).
% 0.36/0.60  thf('87', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.36/0.60      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.36/0.60  thf('88', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['55', '87'])).
% 0.36/0.60  thf('89', plain, ($false), inference('demod', [status(thm)], ['0', '88'])).
% 0.36/0.60  
% 0.36/0.60  % SZS output end Refutation
% 0.36/0.60  
% 0.36/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
