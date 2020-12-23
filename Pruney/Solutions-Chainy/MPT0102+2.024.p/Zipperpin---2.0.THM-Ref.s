%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wkQe3yxUYQ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:01 EST 2020

% Result     : Theorem 52.22s
% Output     : Refutation 52.22s
% Verified   : 
% Statistics : Number of formulae       :  480 (133316 expanded)
%              Number of leaves         :   14 (46798 expanded)
%              Depth                    :   37
%              Number of atoms          : 5002 (1193704 expanded)
%              Number of equality atoms :  473 (133309 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t95_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['21','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('47',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('51',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['48','64'])).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','73'])).

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','76'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('81',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('87',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('88',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k5_xboole_0 @ X3 @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['85','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('96',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('97',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['93','94','99','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['78','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['77','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['78','103'])).

thf('107',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('108',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['108','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['78','103'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106','107','114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106','107','114','115'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('119',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('120',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('121',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('122',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['120','125'])).

thf('127',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('129',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('130',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['126','127','128','129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['48','64'])).

thf('133',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['48','64'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['131','137','140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 )
      = X2 ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['119','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['118','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['48','64'])).

thf('150',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['153','157'])).

thf('159',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31','32','33'])).

thf('163',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['164','169'])).

thf('171',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('172',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('173',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('174',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['170','171','172','173','174'])).

thf('176',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('177',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('178',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['176','181'])).

thf('183',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('184',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106','107','114','115'])).

thf('186',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('191',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('193',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106','107','114','115'])).

thf('195',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['197','200'])).

thf('202',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['196','203'])).

thf('205',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['184','185','186','187','188','195','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['175','205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('209',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('210',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('211',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['208','211'])).

thf('213',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['212','213','214','215'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['207','219'])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['161','220'])).

thf('222',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['148','221'])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('224',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','98'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['207','219'])).

thf('227',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['222','223','224','225','226'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('231',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106','107','114','115'])).

thf('232',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106','107','114','115'])).

thf('233',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['222','223','224','225','226'])).

thf('234',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('236',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('238',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['236','237'])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('241',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('245',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['243','244'])).

thf('246',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('247',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('250',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['251','252'])).

thf('254',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('256',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('257',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('258',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('260',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('261',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['258','259','260'])).

thf('262',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('263',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['261','262'])).

thf('264',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('265',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['255','265'])).

thf('267',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('268',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['263','264'])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('270',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['266','267','268','269'])).

thf('271',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['248','270'])).

thf('272',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['248','270'])).

thf('273',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['247','271','272'])).

thf('274',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['238','273'])).

thf('275',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('276',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('277',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('278',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('279',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('280',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('281',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['279','280'])).

thf('282',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['278','281'])).

thf('283',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['277','282'])).

thf('284',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['276','283'])).

thf('285',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['248','270'])).

thf('286',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('287',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('288',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('289',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['287','288'])).

thf('290',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('291',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('292',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['289','290','291'])).

thf('293',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['78','103'])).

thf('294',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['292','293'])).

thf('295',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['286','294'])).

thf('296',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('297',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('298',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('299',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('300',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('301',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('302',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['295','296','297','298','299','300','301'])).

thf('303',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['274','275','284','285','302'])).

thf('304',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('305',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','98'])).

thf('306',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('307',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('308',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['306','307'])).

thf('309',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['266','267','268','269'])).

thf('310',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['308','309'])).

thf('311',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['266','267','268','269'])).

thf('312',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('313',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['266','267','268','269'])).

thf('314',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['310','311','312','313'])).

thf('315',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('316',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['279','280'])).

thf('317',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('318',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('319',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['317','318'])).

thf('320',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('321',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['319','320'])).

thf('322',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X3 ) @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X3 ) @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['316','321'])).

thf('323',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('324',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('325',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X3 ) @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X3 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['322','323','324'])).

thf('326',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['78','103'])).

thf('327',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106','107','114','115'])).

thf('328',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['326','327'])).

thf('329',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['326','327'])).

thf('330',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X3 @ ( k4_xboole_0 @ X0 @ X2 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['325','328','329'])).

thf('331',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('332',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['37','116','117','227','228','229','230','231','232','233','234','235','303','304','305','314','315','330','331'])).

thf('333',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['14','332'])).

thf('334',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('335',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('336',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('337',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['335','336'])).

thf('338',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['334','337'])).

thf('339',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['209','210'])).

thf('340',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['338','339'])).

thf('341',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('342',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('343',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('344',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['340','341','342','343'])).

thf('345',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['326','327'])).

thf('346',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('347',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('348',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['346','347'])).

thf('349',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('350',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['348','349'])).

thf('351',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('352',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['350','351'])).

thf('353',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('354',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['352','353'])).

thf('355',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('356',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['207','219'])).

thf('357',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['355','356'])).

thf('358',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['222','223','224','225','226'])).

thf('359',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['326','327'])).

thf('360',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('361',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('362',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['360','361'])).

thf('363',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('364',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('365',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['362','363','364'])).

thf('366',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('367',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('368',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['365','366','367'])).

thf('369',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['207','219'])).

thf('370',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('371',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('372',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['370','371'])).

thf('373',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('374',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('375',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('376',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('377',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('378',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['376','377'])).

thf('379',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('380',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['378','379'])).

thf('381',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('382',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('383',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['380','381','382'])).

thf('384',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['335','336'])).

thf('385',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('386',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['383','384','385'])).

thf('387',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['375','386'])).

thf('388',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['372','373','374','387'])).

thf('389',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['207','219'])).

thf('390',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['368','369','388','389'])).

thf('391',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['354','357','358','359','390'])).

thf('392',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','76'])).

thf('393',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['391','392'])).

thf('394',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('395',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['108','113'])).

thf('396',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['393','394','395'])).

thf('397',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['326','327'])).

thf('398',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['344','345','396','397'])).

thf('399',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('400',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['295','296','297','298','299','300','301'])).

thf('401',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('402',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('403',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['401','402'])).

thf('404',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('405',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('406',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['404','405'])).

thf('407',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('408',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('409',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('410',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('411',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['406','407','408','409','410'])).

thf('412',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['403','411'])).

thf('413',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('414',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['412','413'])).

thf('415',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('416',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('417',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['415','416'])).

thf('418',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['207','219'])).

thf('419',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['417','418'])).

thf('420',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['344','345','396','397'])).

thf('421',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('422',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('423',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('424',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('425',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['423','424'])).

thf('426',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X1 ) ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['422','425'])).

thf('427',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('428',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('429',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['426','427','428'])).

thf('430',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('431',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['319','320'])).

thf('432',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['430','431'])).

thf('433',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('434',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('435',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['432','433','434'])).

thf('436',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['429','435'])).

thf('437',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['333','398','399','400','414','419','420','421','436'])).

thf('438',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('439',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['207','219'])).

thf('440',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['438','439'])).

thf('441',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['437','440'])).

thf('442',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('443',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('444',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('445',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['443','444'])).

thf('446',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('447',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('448',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['445','446','447'])).

thf('449',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['442','448'])).

thf('450',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('451',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('452',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['372','373','374','387'])).

thf('453',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('454',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('455',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('456',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['449','450','451','452','453','454','455'])).

thf('457',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('458',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['456','457'])).

thf('459',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['108','113'])).

thf('460',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['458','459'])).

thf('461',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['441','460'])).

thf('462',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('463',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','461','462'])).

thf('464',plain,(
    $false ),
    inference(simplify,[status(thm)],['463'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wkQe3yxUYQ
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:33:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 52.22/52.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 52.22/52.45  % Solved by: fo/fo7.sh
% 52.22/52.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 52.22/52.45  % done 13599 iterations in 51.985s
% 52.22/52.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 52.22/52.45  % SZS output start Refutation
% 52.22/52.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 52.22/52.45  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 52.22/52.45  thf(sk_B_type, type, sk_B: $i).
% 52.22/52.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 52.22/52.45  thf(sk_A_type, type, sk_A: $i).
% 52.22/52.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 52.22/52.45  thf(t95_xboole_1, conjecture,
% 52.22/52.45    (![A:$i,B:$i]:
% 52.22/52.45     ( ( k3_xboole_0 @ A @ B ) =
% 52.22/52.45       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 52.22/52.45  thf(zf_stmt_0, negated_conjecture,
% 52.22/52.45    (~( ![A:$i,B:$i]:
% 52.22/52.45        ( ( k3_xboole_0 @ A @ B ) =
% 52.22/52.45          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 52.22/52.45    inference('cnf.neg', [status(esa)], [t95_xboole_1])).
% 52.22/52.45  thf('0', plain,
% 52.22/52.45      (((k3_xboole_0 @ sk_A @ sk_B)
% 52.22/52.45         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 52.22/52.45             (k2_xboole_0 @ sk_A @ sk_B)))),
% 52.22/52.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.22/52.45  thf(commutativity_k3_xboole_0, axiom,
% 52.22/52.45    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 52.22/52.45  thf('1', plain,
% 52.22/52.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.45  thf(t51_xboole_1, axiom,
% 52.22/52.45    (![A:$i,B:$i]:
% 52.22/52.45     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 52.22/52.45       ( A ) ))).
% 52.22/52.45  thf('2', plain,
% 52.22/52.45      (![X13 : $i, X14 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 52.22/52.45           = (X13))),
% 52.22/52.45      inference('cnf', [status(esa)], [t51_xboole_1])).
% 52.22/52.45  thf('3', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 52.22/52.45           = (X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['1', '2'])).
% 52.22/52.45  thf(t48_xboole_1, axiom,
% 52.22/52.45    (![A:$i,B:$i]:
% 52.22/52.45     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 52.22/52.45  thf('4', plain,
% 52.22/52.45      (![X11 : $i, X12 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 52.22/52.45           = (k3_xboole_0 @ X11 @ X12))),
% 52.22/52.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 52.22/52.45  thf(t39_xboole_1, axiom,
% 52.22/52.45    (![A:$i,B:$i]:
% 52.22/52.45     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 52.22/52.45  thf('5', plain,
% 52.22/52.45      (![X6 : $i, X7 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 52.22/52.45           = (k2_xboole_0 @ X6 @ X7))),
% 52.22/52.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 52.22/52.45  thf('6', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['4', '5'])).
% 52.22/52.45  thf(commutativity_k2_xboole_0, axiom,
% 52.22/52.45    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 52.22/52.45  thf('7', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.45  thf('8', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.45  thf('9', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 52.22/52.45      inference('demod', [status(thm)], ['6', '7', '8'])).
% 52.22/52.45  thf('10', plain,
% 52.22/52.45      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['3', '9'])).
% 52.22/52.45  thf('11', plain,
% 52.22/52.45      (![X6 : $i, X7 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 52.22/52.45           = (k2_xboole_0 @ X6 @ X7))),
% 52.22/52.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 52.22/52.45  thf('12', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 52.22/52.45      inference('demod', [status(thm)], ['10', '11'])).
% 52.22/52.45  thf(d6_xboole_0, axiom,
% 52.22/52.45    (![A:$i,B:$i]:
% 52.22/52.45     ( ( k5_xboole_0 @ A @ B ) =
% 52.22/52.45       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 52.22/52.45  thf('13', plain,
% 52.22/52.45      (![X4 : $i, X5 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X4 @ X5)
% 52.22/52.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 52.22/52.45      inference('cnf', [status(esa)], [d6_xboole_0])).
% 52.22/52.45  thf('14', plain,
% 52.22/52.45      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['12', '13'])).
% 52.22/52.45  thf(t41_xboole_1, axiom,
% 52.22/52.45    (![A:$i,B:$i,C:$i]:
% 52.22/52.45     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 52.22/52.45       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 52.22/52.45  thf('15', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('16', plain,
% 52.22/52.45      (![X11 : $i, X12 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 52.22/52.45           = (k3_xboole_0 @ X11 @ X12))),
% 52.22/52.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 52.22/52.45  thf('17', plain,
% 52.22/52.45      (![X11 : $i, X12 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 52.22/52.45           = (k3_xboole_0 @ X11 @ X12))),
% 52.22/52.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 52.22/52.45  thf('18', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['16', '17'])).
% 52.22/52.45  thf('19', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X2 @ 
% 52.22/52.45           (k2_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 52.22/52.45           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 52.22/52.45              (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['15', '18'])).
% 52.22/52.45  thf('20', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('21', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X2 @ 
% 52.22/52.45           (k2_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 52.22/52.45           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 52.22/52.45              (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 52.22/52.45      inference('demod', [status(thm)], ['19', '20'])).
% 52.22/52.45  thf('22', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 52.22/52.45      inference('demod', [status(thm)], ['10', '11'])).
% 52.22/52.45  thf('23', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('24', plain,
% 52.22/52.45      (![X4 : $i, X5 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X4 @ X5)
% 52.22/52.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 52.22/52.45      inference('cnf', [status(esa)], [d6_xboole_0])).
% 52.22/52.45  thf('25', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 52.22/52.45           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.45              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 52.22/52.45      inference('sup+', [status(thm)], ['23', '24'])).
% 52.22/52.45  thf('26', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 52.22/52.45           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 52.22/52.45              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 52.22/52.45      inference('sup+', [status(thm)], ['22', '25'])).
% 52.22/52.45  thf('27', plain,
% 52.22/52.45      (![X4 : $i, X5 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X4 @ X5)
% 52.22/52.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 52.22/52.45      inference('cnf', [status(esa)], [d6_xboole_0])).
% 52.22/52.45  thf('28', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.45  thf('29', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k5_xboole_0 @ X1 @ X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['27', '28'])).
% 52.22/52.45  thf('30', plain,
% 52.22/52.45      (![X4 : $i, X5 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X4 @ X5)
% 52.22/52.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 52.22/52.45      inference('cnf', [status(esa)], [d6_xboole_0])).
% 52.22/52.45  thf('31', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['29', '30'])).
% 52.22/52.45  thf('32', plain,
% 52.22/52.45      (![X6 : $i, X7 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 52.22/52.45           = (k2_xboole_0 @ X6 @ X7))),
% 52.22/52.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 52.22/52.45  thf('33', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.45  thf('34', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 52.22/52.45      inference('demod', [status(thm)], ['26', '31', '32', '33'])).
% 52.22/52.45  thf('35', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ 
% 52.22/52.45           (k2_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)) @ 
% 52.22/52.45           (k4_xboole_0 @ X2 @ 
% 52.22/52.45            (k2_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))
% 52.22/52.45           = (k2_xboole_0 @ 
% 52.22/52.45              (k2_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)) @ 
% 52.22/52.45              (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 52.22/52.45               (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 52.22/52.45      inference('sup+', [status(thm)], ['21', '34'])).
% 52.22/52.45  thf('36', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X2 @ 
% 52.22/52.45           (k2_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 52.22/52.45           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 52.22/52.45              (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 52.22/52.45      inference('demod', [status(thm)], ['19', '20'])).
% 52.22/52.45  thf('37', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ 
% 52.22/52.45           (k2_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)) @ 
% 52.22/52.45           (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 52.22/52.45            (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 52.22/52.45           = (k2_xboole_0 @ 
% 52.22/52.45              (k2_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)) @ 
% 52.22/52.45              (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 52.22/52.45               (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 52.22/52.45      inference('demod', [status(thm)], ['35', '36'])).
% 52.22/52.45  thf('38', plain,
% 52.22/52.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.45  thf('39', plain,
% 52.22/52.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.45  thf('40', plain,
% 52.22/52.45      (![X11 : $i, X12 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 52.22/52.45           = (k3_xboole_0 @ X11 @ X12))),
% 52.22/52.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 52.22/52.45  thf('41', plain,
% 52.22/52.45      (![X13 : $i, X14 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 52.22/52.45           = (X13))),
% 52.22/52.45      inference('cnf', [status(esa)], [t51_xboole_1])).
% 52.22/52.45  thf('42', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.45           (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['40', '41'])).
% 52.22/52.45  thf('43', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.45  thf('44', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 52.22/52.45           (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 52.22/52.45      inference('demod', [status(thm)], ['42', '43'])).
% 52.22/52.45  thf('45', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 52.22/52.45           (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))) = (X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['39', '44'])).
% 52.22/52.45  thf('46', plain,
% 52.22/52.45      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['12', '13'])).
% 52.22/52.45  thf('47', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('48', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 52.22/52.45           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['46', '47'])).
% 52.22/52.45  thf('49', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 52.22/52.45           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['46', '47'])).
% 52.22/52.45  thf('50', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 52.22/52.45      inference('demod', [status(thm)], ['6', '7', '8'])).
% 52.22/52.45  thf('51', plain,
% 52.22/52.45      (![X13 : $i, X14 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 52.22/52.45           = (X13))),
% 52.22/52.45      inference('cnf', [status(esa)], [t51_xboole_1])).
% 52.22/52.45  thf('52', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['50', '51'])).
% 52.22/52.45  thf('53', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))
% 52.22/52.45           = (X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['49', '52'])).
% 52.22/52.45  thf('54', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 52.22/52.45           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['46', '47'])).
% 52.22/52.45  thf('55', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ 
% 52.22/52.45           (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))
% 52.22/52.45           = (k4_xboole_0 @ X0 @ X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['53', '54'])).
% 52.22/52.45  thf('56', plain,
% 52.22/52.45      (![X11 : $i, X12 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 52.22/52.45           = (k3_xboole_0 @ X11 @ X12))),
% 52.22/52.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 52.22/52.45  thf('57', plain,
% 52.22/52.45      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['12', '13'])).
% 52.22/52.45  thf('58', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 52.22/52.45           = (k5_xboole_0 @ X0 @ X0))),
% 52.22/52.45      inference('demod', [status(thm)], ['55', '56', '57'])).
% 52.22/52.45  thf('59', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 52.22/52.45           = (X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['1', '2'])).
% 52.22/52.45  thf('60', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ 
% 52.22/52.45           (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))) = (X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['58', '59'])).
% 52.22/52.45  thf('61', plain,
% 52.22/52.45      (![X6 : $i, X7 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 52.22/52.45           = (k2_xboole_0 @ X6 @ X7))),
% 52.22/52.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 52.22/52.45  thf('62', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 52.22/52.45      inference('demod', [status(thm)], ['60', '61'])).
% 52.22/52.45  thf('63', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['50', '51'])).
% 52.22/52.45  thf('64', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 52.22/52.45           = (k5_xboole_0 @ X1 @ X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['62', '63'])).
% 52.22/52.45  thf('65', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X0 @ X0)
% 52.22/52.45           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['48', '64'])).
% 52.22/52.45  thf('66', plain,
% 52.22/52.45      (![X11 : $i, X12 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 52.22/52.45           = (k3_xboole_0 @ X11 @ X12))),
% 52.22/52.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 52.22/52.45  thf('67', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 52.22/52.45           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['65', '66'])).
% 52.22/52.45  thf('68', plain,
% 52.22/52.45      (![X6 : $i, X7 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 52.22/52.45           = (k2_xboole_0 @ X6 @ X7))),
% 52.22/52.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 52.22/52.45  thf('69', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 52.22/52.45      inference('demod', [status(thm)], ['60', '61'])).
% 52.22/52.45  thf('70', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 52.22/52.45           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['68', '69'])).
% 52.22/52.45  thf('71', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 52.22/52.45      inference('demod', [status(thm)], ['60', '61'])).
% 52.22/52.45  thf('72', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((X0) = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['70', '71'])).
% 52.22/52.45  thf('73', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['67', '72'])).
% 52.22/52.45  thf('74', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ X1 @ X0)
% 52.22/52.45           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['45', '73'])).
% 52.22/52.45  thf('75', plain,
% 52.22/52.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.45  thf('76', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ X1 @ X0)
% 52.22/52.45           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 52.22/52.45      inference('demod', [status(thm)], ['74', '75'])).
% 52.22/52.45  thf('77', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ X0 @ X1)
% 52.22/52.45           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['38', '76'])).
% 52.22/52.45  thf('78', plain,
% 52.22/52.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.45  thf('79', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 52.22/52.45           = (k5_xboole_0 @ X0 @ X0))),
% 52.22/52.45      inference('demod', [status(thm)], ['55', '56', '57'])).
% 52.22/52.45  thf('80', plain,
% 52.22/52.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.45  thf('81', plain,
% 52.22/52.45      (![X11 : $i, X12 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 52.22/52.45           = (k3_xboole_0 @ X11 @ X12))),
% 52.22/52.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 52.22/52.45  thf('82', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['50', '51'])).
% 52.22/52.45  thf('83', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['81', '82'])).
% 52.22/52.45  thf('84', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['80', '83'])).
% 52.22/52.45  thf('85', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['79', '84'])).
% 52.22/52.45  thf('86', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('87', plain,
% 52.22/52.45      (![X11 : $i, X12 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 52.22/52.45           = (k3_xboole_0 @ X11 @ X12))),
% 52.22/52.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 52.22/52.45  thf('88', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('89', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 52.22/52.45           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['87', '88'])).
% 52.22/52.45  thf('90', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X1) @ X0)
% 52.22/52.45           = (k4_xboole_0 @ X3 @ 
% 52.22/52.45              (k2_xboole_0 @ X2 @ 
% 52.22/52.45               (k2_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X1) @ X0))))),
% 52.22/52.45      inference('sup+', [status(thm)], ['86', '89'])).
% 52.22/52.45  thf('91', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('92', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X1) @ X0)
% 52.22/52.45           = (k4_xboole_0 @ X3 @ 
% 52.22/52.45              (k2_xboole_0 @ X2 @ 
% 52.22/52.45               (k2_xboole_0 @ (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ X1)) @ X0))))),
% 52.22/52.45      inference('demod', [status(thm)], ['90', '91'])).
% 52.22/52.45  thf('93', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 52.22/52.45           (k5_xboole_0 @ X3 @ X3))
% 52.22/52.45           = (k4_xboole_0 @ X2 @ 
% 52.22/52.45              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 52.22/52.45      inference('sup+', [status(thm)], ['85', '92'])).
% 52.22/52.45  thf('94', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((X0) = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['70', '71'])).
% 52.22/52.45  thf('95', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.45  thf('96', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('97', plain,
% 52.22/52.45      (![X6 : $i, X7 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 52.22/52.45           = (k2_xboole_0 @ X6 @ X7))),
% 52.22/52.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 52.22/52.45  thf('98', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.45           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['96', '97'])).
% 52.22/52.45  thf('99', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.45           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['95', '98'])).
% 52.22/52.45  thf('100', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.45  thf('101', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 52.22/52.45           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['87', '88'])).
% 52.22/52.45  thf('102', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 52.22/52.45           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 52.22/52.45      inference('sup+', [status(thm)], ['100', '101'])).
% 52.22/52.45  thf('103', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 52.22/52.45           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X1))),
% 52.22/52.45      inference('demod', [status(thm)], ['93', '94', '99', '102'])).
% 52.22/52.45  thf('104', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)
% 52.22/52.45           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.45      inference('sup+', [status(thm)], ['78', '103'])).
% 52.22/52.45  thf('105', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ X0)
% 52.22/52.45           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.45      inference('sup+', [status(thm)], ['77', '104'])).
% 52.22/52.45  thf('106', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)
% 52.22/52.45           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.45      inference('sup+', [status(thm)], ['78', '103'])).
% 52.22/52.45  thf('107', plain,
% 52.22/52.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.45  thf('108', plain,
% 52.22/52.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.45  thf('109', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 52.22/52.45           (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 52.22/52.45      inference('demod', [status(thm)], ['42', '43'])).
% 52.22/52.45  thf('110', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['67', '72'])).
% 52.22/52.45  thf('111', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ X0 @ X1)
% 52.22/52.45           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['109', '110'])).
% 52.22/52.45  thf('112', plain,
% 52.22/52.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.45  thf('113', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ X0 @ X1)
% 52.22/52.45           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['111', '112'])).
% 52.22/52.45  thf('114', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ X0 @ X1)
% 52.22/52.45           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['108', '113'])).
% 52.22/52.45  thf('115', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)
% 52.22/52.45           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.45      inference('sup+', [status(thm)], ['78', '103'])).
% 52.22/52.45  thf('116', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 52.22/52.45           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 52.22/52.45      inference('demod', [status(thm)], ['105', '106', '107', '114', '115'])).
% 52.22/52.45  thf('117', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 52.22/52.45           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 52.22/52.45      inference('demod', [status(thm)], ['105', '106', '107', '114', '115'])).
% 52.22/52.45  thf('118', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.45  thf('119', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('120', plain,
% 52.22/52.45      (![X6 : $i, X7 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 52.22/52.45           = (k2_xboole_0 @ X6 @ X7))),
% 52.22/52.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 52.22/52.45  thf('121', plain,
% 52.22/52.45      (![X11 : $i, X12 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 52.22/52.45           = (k3_xboole_0 @ X11 @ X12))),
% 52.22/52.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 52.22/52.45  thf('122', plain,
% 52.22/52.45      (![X4 : $i, X5 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X4 @ X5)
% 52.22/52.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 52.22/52.45      inference('cnf', [status(esa)], [d6_xboole_0])).
% 52.22/52.45  thf('123', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 52.22/52.45              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['121', '122'])).
% 52.22/52.45  thf('124', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('125', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 52.22/52.45              (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))))),
% 52.22/52.45      inference('demod', [status(thm)], ['123', '124'])).
% 52.22/52.45  thf('126', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 52.22/52.45           (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))
% 52.22/52.45           = (k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1) @ 
% 52.22/52.45              (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))))),
% 52.22/52.45      inference('sup+', [status(thm)], ['120', '125'])).
% 52.22/52.45  thf('127', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('128', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 52.22/52.45      inference('demod', [status(thm)], ['10', '11'])).
% 52.22/52.45  thf('129', plain,
% 52.22/52.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.45  thf('130', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('131', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 52.22/52.45           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 52.22/52.45              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))))),
% 52.22/52.45      inference('demod', [status(thm)], ['126', '127', '128', '129', '130'])).
% 52.22/52.45  thf('132', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X0 @ X0)
% 52.22/52.45           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['48', '64'])).
% 52.22/52.45  thf('133', plain,
% 52.22/52.45      (![X6 : $i, X7 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 52.22/52.45           = (k2_xboole_0 @ X6 @ X7))),
% 52.22/52.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 52.22/52.45  thf('134', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0))
% 52.22/52.45           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['132', '133'])).
% 52.22/52.45  thf('135', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['79', '84'])).
% 52.22/52.45  thf('136', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.45  thf('137', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X0 @ X1)
% 52.22/52.45           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['134', '135', '136'])).
% 52.22/52.45  thf('138', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.45  thf('139', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X0 @ X0)
% 52.22/52.45           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['48', '64'])).
% 52.22/52.45  thf('140', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X0 @ X0)
% 52.22/52.45           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['138', '139'])).
% 52.22/52.45  thf('141', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['79', '84'])).
% 52.22/52.45  thf('142', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 52.22/52.45           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['131', '137', '140', '141'])).
% 52.22/52.45  thf('143', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 52.22/52.45      inference('demod', [status(thm)], ['60', '61'])).
% 52.22/52.45  thf('144', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2)
% 52.22/52.45           = (X2))),
% 52.22/52.45      inference('sup+', [status(thm)], ['142', '143'])).
% 52.22/52.45  thf('145', plain,
% 52.22/52.45      (![X13 : $i, X14 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 52.22/52.45           = (X13))),
% 52.22/52.45      inference('cnf', [status(esa)], [t51_xboole_1])).
% 52.22/52.45  thf('146', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['144', '145'])).
% 52.22/52.45  thf('147', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.45           = (X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['119', '146'])).
% 52.22/52.45  thf('148', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.45           = (X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['118', '147'])).
% 52.22/52.45  thf('149', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X0 @ X0)
% 52.22/52.45           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['48', '64'])).
% 52.22/52.45  thf('150', plain,
% 52.22/52.45      (![X4 : $i, X5 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X4 @ X5)
% 52.22/52.45           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 52.22/52.45      inference('cnf', [status(esa)], [d6_xboole_0])).
% 52.22/52.45  thf('151', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 52.22/52.45           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ 
% 52.22/52.45              (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['149', '150'])).
% 52.22/52.45  thf('152', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 52.22/52.45      inference('demod', [status(thm)], ['60', '61'])).
% 52.22/52.45  thf('153', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 52.22/52.45           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 52.22/52.45      inference('demod', [status(thm)], ['151', '152'])).
% 52.22/52.45  thf('154', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 52.22/52.45              (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))))),
% 52.22/52.45      inference('demod', [status(thm)], ['123', '124'])).
% 52.22/52.45  thf('155', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X0 @ X0)
% 52.22/52.45           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['138', '139'])).
% 52.22/52.45  thf('156', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['79', '84'])).
% 52.22/52.45  thf('157', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k3_xboole_0 @ X1 @ X0))),
% 52.22/52.45      inference('demod', [status(thm)], ['154', '155', '156'])).
% 52.22/52.45  thf('158', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 52.22/52.45           (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.45           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['153', '157'])).
% 52.22/52.45  thf('159', plain,
% 52.22/52.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.45  thf('160', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['67', '72'])).
% 52.22/52.45  thf('161', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 52.22/52.45           (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))) = (X1))),
% 52.22/52.45      inference('demod', [status(thm)], ['158', '159', '160'])).
% 52.22/52.45  thf('162', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 52.22/52.45      inference('demod', [status(thm)], ['26', '31', '32', '33'])).
% 52.22/52.45  thf('163', plain,
% 52.22/52.45      (![X6 : $i, X7 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 52.22/52.45           = (k2_xboole_0 @ X6 @ X7))),
% 52.22/52.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 52.22/52.45  thf('164', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['162', '163'])).
% 52.22/52.45  thf('165', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k5_xboole_0 @ X1 @ X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['27', '28'])).
% 52.22/52.45  thf('166', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['67', '72'])).
% 52.22/52.45  thf('167', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X0 @ X1)
% 52.22/52.45           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['165', '166'])).
% 52.22/52.45  thf('168', plain,
% 52.22/52.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.45  thf('169', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X0 @ X1)
% 52.22/52.45           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['167', '168'])).
% 52.22/52.45  thf('170', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 52.22/52.45           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 52.22/52.45              (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['164', '169'])).
% 52.22/52.45  thf('171', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('172', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 52.22/52.45      inference('demod', [status(thm)], ['10', '11'])).
% 52.22/52.45  thf('173', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('174', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 52.22/52.45      inference('demod', [status(thm)], ['10', '11'])).
% 52.22/52.45  thf('175', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X0 @ X1)
% 52.22/52.45           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['170', '171', '172', '173', '174'])).
% 52.22/52.45  thf('176', plain,
% 52.22/52.45      (![X13 : $i, X14 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 52.22/52.45           = (X13))),
% 52.22/52.45      inference('cnf', [status(esa)], [t51_xboole_1])).
% 52.22/52.45  thf('177', plain,
% 52.22/52.45      (![X11 : $i, X12 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 52.22/52.45           = (k3_xboole_0 @ X11 @ X12))),
% 52.22/52.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 52.22/52.45  thf('178', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('179', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 52.22/52.45           = (k4_xboole_0 @ X2 @ 
% 52.22/52.45              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 52.22/52.45      inference('sup+', [status(thm)], ['177', '178'])).
% 52.22/52.45  thf('180', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('181', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 52.22/52.45           = (k4_xboole_0 @ X2 @ 
% 52.22/52.45              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 52.22/52.45      inference('demod', [status(thm)], ['179', '180'])).
% 52.22/52.45  thf('182', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 52.22/52.45           (k4_xboole_0 @ X0 @ X1))
% 52.22/52.45           = (k4_xboole_0 @ X2 @ 
% 52.22/52.45              (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))))),
% 52.22/52.45      inference('sup+', [status(thm)], ['176', '181'])).
% 52.22/52.45  thf('183', plain,
% 52.22/52.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.45  thf('184', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 52.22/52.45           (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))
% 52.22/52.45           = (k4_xboole_0 @ X2 @ 
% 52.22/52.45              (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))))),
% 52.22/52.45      inference('demod', [status(thm)], ['182', '183'])).
% 52.22/52.45  thf('185', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 52.22/52.45           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 52.22/52.45      inference('demod', [status(thm)], ['105', '106', '107', '114', '115'])).
% 52.22/52.45  thf('186', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('187', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.45  thf('188', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['80', '83'])).
% 52.22/52.45  thf('189', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.45  thf('190', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 52.22/52.45           = (k4_xboole_0 @ X2 @ 
% 52.22/52.45              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 52.22/52.45      inference('demod', [status(thm)], ['179', '180'])).
% 52.22/52.45  thf('191', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 52.22/52.45           = (k4_xboole_0 @ X2 @ 
% 52.22/52.45              (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 52.22/52.45      inference('sup+', [status(thm)], ['189', '190'])).
% 52.22/52.45  thf('192', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.45           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['96', '97'])).
% 52.22/52.45  thf('193', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 52.22/52.45           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 52.22/52.45      inference('demod', [status(thm)], ['191', '192'])).
% 52.22/52.45  thf('194', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 52.22/52.45           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 52.22/52.45      inference('demod', [status(thm)], ['105', '106', '107', '114', '115'])).
% 52.22/52.45  thf('195', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 52.22/52.45      inference('demod', [status(thm)], ['193', '194'])).
% 52.22/52.45  thf('196', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['16', '17'])).
% 52.22/52.45  thf('197', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['50', '51'])).
% 52.22/52.45  thf('198', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.45  thf('199', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['67', '72'])).
% 52.22/52.45  thf('200', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 52.22/52.45      inference('sup+', [status(thm)], ['198', '199'])).
% 52.22/52.45  thf('201', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X0 @ X1)
% 52.22/52.45           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['197', '200'])).
% 52.22/52.45  thf('202', plain,
% 52.22/52.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.45  thf('203', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X0 @ X1)
% 52.22/52.45           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)], ['201', '202'])).
% 52.22/52.45  thf('204', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 52.22/52.45           = (k4_xboole_0 @ X1 @ X0))),
% 52.22/52.45      inference('demod', [status(thm)], ['196', '203'])).
% 52.22/52.45  thf('205', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 52.22/52.45           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 52.22/52.45      inference('demod', [status(thm)],
% 52.22/52.45                ['184', '185', '186', '187', '188', '195', '204'])).
% 52.22/52.45  thf('206', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 52.22/52.45           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 52.22/52.45      inference('demod', [status(thm)], ['151', '152'])).
% 52.22/52.45  thf('207', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ X0 @ X1)
% 52.22/52.45           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 52.22/52.45      inference('demod', [status(thm)], ['175', '205', '206'])).
% 52.22/52.45  thf('208', plain,
% 52.22/52.45      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 52.22/52.45      inference('sup+', [status(thm)], ['12', '13'])).
% 52.22/52.45  thf('209', plain,
% 52.22/52.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.45         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.45           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.45  thf('210', plain,
% 52.22/52.45      (![X13 : $i, X14 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 52.22/52.45           = (X13))),
% 52.22/52.45      inference('cnf', [status(esa)], [t51_xboole_1])).
% 52.22/52.45  thf('211', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 52.22/52.45           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.45           = (k4_xboole_0 @ X2 @ X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['209', '210'])).
% 52.22/52.45  thf('212', plain,
% 52.22/52.45      (![X0 : $i, X1 : $i]:
% 52.22/52.45         ((k2_xboole_0 @ 
% 52.22/52.45           (k3_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0) @ 
% 52.22/52.45           (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.45           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 52.22/52.45      inference('sup+', [status(thm)], ['208', '211'])).
% 52.22/52.46  thf('213', plain,
% 52.22/52.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.46  thf('214', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('215', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['60', '61'])).
% 52.22/52.46  thf('216', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 52.22/52.46           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['212', '213', '214', '215'])).
% 52.22/52.46  thf('217', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['151', '152'])).
% 52.22/52.46  thf('218', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['151', '152'])).
% 52.22/52.46  thf('219', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('demod', [status(thm)], ['216', '217', '218'])).
% 52.22/52.46  thf('220', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X1 @ X0)
% 52.22/52.46           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['207', '219'])).
% 52.22/52.46  thf('221', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['161', '220'])).
% 52.22/52.46  thf('222', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ 
% 52.22/52.46           (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ X0) @ 
% 52.22/52.46           X0) = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['148', '221'])).
% 52.22/52.46  thf('223', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('224', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['95', '98'])).
% 52.22/52.46  thf('225', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['29', '30'])).
% 52.22/52.46  thf('226', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X1 @ X0)
% 52.22/52.46           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['207', '219'])).
% 52.22/52.46  thf('227', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 52.22/52.46           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['222', '223', '224', '225', '226'])).
% 52.22/52.46  thf('228', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['134', '135', '136'])).
% 52.22/52.46  thf('229', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['201', '202'])).
% 52.22/52.46  thf('230', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['29', '30'])).
% 52.22/52.46  thf('231', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 52.22/52.46           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['105', '106', '107', '114', '115'])).
% 52.22/52.46  thf('232', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 52.22/52.46           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['105', '106', '107', '114', '115'])).
% 52.22/52.46  thf('233', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 52.22/52.46           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['222', '223', '224', '225', '226'])).
% 52.22/52.46  thf('234', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['134', '135', '136'])).
% 52.22/52.46  thf('235', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['201', '202'])).
% 52.22/52.46  thf('236', plain,
% 52.22/52.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.46           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.46      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.46  thf('237', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['1', '2'])).
% 52.22/52.46  thf('238', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)) @ 
% 52.22/52.46           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k4_xboole_0 @ X2 @ X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['236', '237'])).
% 52.22/52.46  thf('239', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['198', '199'])).
% 52.22/52.46  thf('240', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['1', '2'])).
% 52.22/52.46  thf('241', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))
% 52.22/52.46           = (k2_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['239', '240'])).
% 52.22/52.46  thf('242', plain,
% 52.22/52.46      (![X6 : $i, X7 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 52.22/52.46           = (k2_xboole_0 @ X6 @ X7))),
% 52.22/52.46      inference('cnf', [status(esa)], [t39_xboole_1])).
% 52.22/52.46  thf('243', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['241', '242'])).
% 52.22/52.46  thf('244', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['96', '97'])).
% 52.22/52.46  thf('245', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 52.22/52.46           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['243', '244'])).
% 52.22/52.46  thf('246', plain,
% 52.22/52.46      (![X6 : $i, X7 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 52.22/52.46           = (k2_xboole_0 @ X6 @ X7))),
% 52.22/52.46      inference('cnf', [status(esa)], [t39_xboole_1])).
% 52.22/52.46  thf('247', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 52.22/52.46           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0)))),
% 52.22/52.46      inference('demod', [status(thm)], ['245', '246'])).
% 52.22/52.46  thf('248', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('249', plain,
% 52.22/52.46      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['12', '13'])).
% 52.22/52.46  thf('250', plain,
% 52.22/52.46      (![X13 : $i, X14 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 52.22/52.46           = (X13))),
% 52.22/52.46      inference('cnf', [status(esa)], [t51_xboole_1])).
% 52.22/52.46  thf('251', plain,
% 52.22/52.46      (![X0 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0))
% 52.22/52.46           = (X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['249', '250'])).
% 52.22/52.46  thf('252', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('253', plain,
% 52.22/52.46      (![X0 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 52.22/52.46           = (X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['251', '252'])).
% 52.22/52.46  thf('254', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['60', '61'])).
% 52.22/52.46  thf('255', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['253', '254'])).
% 52.22/52.46  thf('256', plain,
% 52.22/52.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.46           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.46      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.46  thf('257', plain,
% 52.22/52.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.46           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.46      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.46  thf('258', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 52.22/52.46           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['256', '257'])).
% 52.22/52.46  thf('259', plain,
% 52.22/52.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.46           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.46      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.46  thf('260', plain,
% 52.22/52.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.46           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.46      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.46  thf('261', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 52.22/52.46           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 52.22/52.46      inference('demod', [status(thm)], ['258', '259', '260'])).
% 52.22/52.46  thf('262', plain,
% 52.22/52.46      (![X11 : $i, X12 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 52.22/52.46           = (k3_xboole_0 @ X11 @ X12))),
% 52.22/52.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 52.22/52.46  thf('263', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X3 @ 
% 52.22/52.46           (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 52.22/52.46           = (k3_xboole_0 @ X3 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['261', '262'])).
% 52.22/52.46  thf('264', plain,
% 52.22/52.46      (![X11 : $i, X12 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 52.22/52.46           = (k3_xboole_0 @ X11 @ X12))),
% 52.22/52.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 52.22/52.46  thf('265', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k3_xboole_0 @ X3 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 52.22/52.46      inference('demod', [status(thm)], ['263', '264'])).
% 52.22/52.46  thf('266', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ 
% 52.22/52.46           (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['255', '265'])).
% 52.22/52.46  thf('267', plain,
% 52.22/52.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.46  thf('268', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k3_xboole_0 @ X3 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 52.22/52.46      inference('demod', [status(thm)], ['263', '264'])).
% 52.22/52.46  thf('269', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['253', '254'])).
% 52.22/52.46  thf('270', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['266', '267', '268', '269'])).
% 52.22/52.46  thf('271', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 52.22/52.46           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.46      inference('sup+', [status(thm)], ['248', '270'])).
% 52.22/52.46  thf('272', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 52.22/52.46           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.46      inference('sup+', [status(thm)], ['248', '270'])).
% 52.22/52.46  thf('273', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 52.22/52.46           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))))),
% 52.22/52.46      inference('demod', [status(thm)], ['247', '271', '272'])).
% 52.22/52.46  thf('274', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ 
% 52.22/52.46           (k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))
% 52.22/52.46           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ (k4_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['238', '273'])).
% 52.22/52.46  thf('275', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('276', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['201', '202'])).
% 52.22/52.46  thf('277', plain,
% 52.22/52.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.46  thf('278', plain,
% 52.22/52.46      (![X11 : $i, X12 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 52.22/52.46           = (k3_xboole_0 @ X11 @ X12))),
% 52.22/52.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 52.22/52.46  thf('279', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 52.22/52.46           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['87', '88'])).
% 52.22/52.46  thf('280', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['50', '51'])).
% 52.22/52.46  thf('281', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 52.22/52.46           = (X2))),
% 52.22/52.46      inference('sup+', [status(thm)], ['279', '280'])).
% 52.22/52.46  thf('282', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 52.22/52.46           = (X2))),
% 52.22/52.46      inference('sup+', [status(thm)], ['278', '281'])).
% 52.22/52.46  thf('283', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['277', '282'])).
% 52.22/52.46  thf('284', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['276', '283'])).
% 52.22/52.46  thf('285', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 52.22/52.46           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.46      inference('sup+', [status(thm)], ['248', '270'])).
% 52.22/52.46  thf('286', plain,
% 52.22/52.46      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['12', '13'])).
% 52.22/52.46  thf('287', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 52.22/52.46           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['87', '88'])).
% 52.22/52.46  thf('288', plain,
% 52.22/52.46      (![X6 : $i, X7 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 52.22/52.46           = (k2_xboole_0 @ X6 @ X7))),
% 52.22/52.46      inference('cnf', [status(esa)], [t39_xboole_1])).
% 52.22/52.46  thf('289', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 52.22/52.46           (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 52.22/52.46           = (k2_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X2))),
% 52.22/52.46      inference('sup+', [status(thm)], ['287', '288'])).
% 52.22/52.46  thf('290', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('291', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('292', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 52.22/52.46           (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 52.22/52.46           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 52.22/52.46      inference('demod', [status(thm)], ['289', '290', '291'])).
% 52.22/52.46  thf('293', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)
% 52.22/52.46           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.46      inference('sup+', [status(thm)], ['78', '103'])).
% 52.22/52.46  thf('294', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ 
% 52.22/52.46           (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 52.22/52.46           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 52.22/52.46      inference('demod', [status(thm)], ['292', '293'])).
% 52.22/52.46  thf('295', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) @ 
% 52.22/52.46           (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))
% 52.22/52.46           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['286', '294'])).
% 52.22/52.46  thf('296', plain,
% 52.22/52.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.46  thf('297', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['201', '202'])).
% 52.22/52.46  thf('298', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['60', '61'])).
% 52.22/52.46  thf('299', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('300', plain,
% 52.22/52.46      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['12', '13'])).
% 52.22/52.46  thf('301', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['60', '61'])).
% 52.22/52.46  thf('302', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('demod', [status(thm)],
% 52.22/52.46                ['295', '296', '297', '298', '299', '300', '301'])).
% 52.22/52.46  thf('303', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1)
% 52.22/52.46           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('demod', [status(thm)], ['274', '275', '284', '285', '302'])).
% 52.22/52.46  thf('304', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('305', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['95', '98'])).
% 52.22/52.46  thf('306', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('307', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['241', '242'])).
% 52.22/52.46  thf('308', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['306', '307'])).
% 52.22/52.46  thf('309', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['266', '267', '268', '269'])).
% 52.22/52.46  thf('310', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2))
% 52.22/52.46           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.46      inference('sup+', [status(thm)], ['308', '309'])).
% 52.22/52.46  thf('311', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['266', '267', '268', '269'])).
% 52.22/52.46  thf('312', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['134', '135', '136'])).
% 52.22/52.46  thf('313', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['266', '267', '268', '269'])).
% 52.22/52.46  thf('314', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 52.22/52.46           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 52.22/52.46      inference('demod', [status(thm)], ['310', '311', '312', '313'])).
% 52.22/52.46  thf('315', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('316', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 52.22/52.46           = (X2))),
% 52.22/52.46      inference('sup+', [status(thm)], ['279', '280'])).
% 52.22/52.46  thf('317', plain,
% 52.22/52.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.46           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.46      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.46  thf('318', plain,
% 52.22/52.46      (![X4 : $i, X5 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X4 @ X5)
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 52.22/52.46      inference('cnf', [status(esa)], [d6_xboole_0])).
% 52.22/52.46  thf('319', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)) @ 
% 52.22/52.46              (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 52.22/52.46      inference('sup+', [status(thm)], ['317', '318'])).
% 52.22/52.46  thf('320', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('321', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.46              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 52.22/52.46      inference('demod', [status(thm)], ['319', '320'])).
% 52.22/52.46  thf('322', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X3) @ X2) @ 
% 52.22/52.46           (k4_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 52.22/52.46              (k4_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X3) @ X2) @ 
% 52.22/52.46               (k4_xboole_0 @ X1 @ X0))))),
% 52.22/52.46      inference('sup+', [status(thm)], ['316', '321'])).
% 52.22/52.46  thf('323', plain,
% 52.22/52.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.46           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.46      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.46  thf('324', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['96', '97'])).
% 52.22/52.46  thf('325', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X3) @ X2) @ 
% 52.22/52.46           (k4_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 52.22/52.46              (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X3) @ X2)))),
% 52.22/52.46      inference('demod', [status(thm)], ['322', '323', '324'])).
% 52.22/52.46  thf('326', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)
% 52.22/52.46           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.46      inference('sup+', [status(thm)], ['78', '103'])).
% 52.22/52.46  thf('327', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 52.22/52.46           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['105', '106', '107', '114', '115'])).
% 52.22/52.46  thf('328', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 52.22/52.46           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.46      inference('demod', [status(thm)], ['326', '327'])).
% 52.22/52.46  thf('329', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 52.22/52.46           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.46      inference('demod', [status(thm)], ['326', '327'])).
% 52.22/52.46  thf('330', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k3_xboole_0 @ X3 @ (k4_xboole_0 @ X0 @ X2)) @ 
% 52.22/52.46           (k4_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 52.22/52.46              (k3_xboole_0 @ X3 @ (k4_xboole_0 @ X0 @ X2))))),
% 52.22/52.46      inference('demod', [status(thm)], ['325', '328', '329'])).
% 52.22/52.46  thf('331', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['29', '30'])).
% 52.22/52.46  thf('332', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.46           (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))))
% 52.22/52.46           = (k2_xboole_0 @ X1 @ 
% 52.22/52.46              (k5_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 52.22/52.46               (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))))),
% 52.22/52.46      inference('demod', [status(thm)],
% 52.22/52.46                ['37', '116', '117', '227', '228', '229', '230', '231', '232', 
% 52.22/52.46                 '233', '234', '235', '303', '304', '305', '314', '315', 
% 52.22/52.46                 '330', '331'])).
% 52.22/52.46  thf('333', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ 
% 52.22/52.46           (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.46           (k2_xboole_0 @ X1 @ 
% 52.22/52.46            (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))))
% 52.22/52.46           = (k2_xboole_0 @ X1 @ 
% 52.22/52.46              (k5_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ 
% 52.22/52.46               (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))))),
% 52.22/52.46      inference('sup+', [status(thm)], ['14', '332'])).
% 52.22/52.46  thf('334', plain,
% 52.22/52.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.46  thf('335', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ X0)
% 52.22/52.46           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['138', '139'])).
% 52.22/52.46  thf('336', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 52.22/52.46           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['87', '88'])).
% 52.22/52.46  thf('337', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 52.22/52.46           = (k5_xboole_0 @ X0 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['335', '336'])).
% 52.22/52.46  thf('338', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 52.22/52.46           = (k5_xboole_0 @ X0 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['334', '337'])).
% 52.22/52.46  thf('339', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 52.22/52.46           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k4_xboole_0 @ X2 @ X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['209', '210'])).
% 52.22/52.46  thf('340', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ 
% 52.22/52.46           (k3_xboole_0 @ 
% 52.22/52.46            (k4_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1) @ 
% 52.22/52.46            X0) @ 
% 52.22/52.46           (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['338', '339'])).
% 52.22/52.46  thf('341', plain,
% 52.22/52.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.46  thf('342', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('343', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['60', '61'])).
% 52.22/52.46  thf('344', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ 
% 52.22/52.46           (k4_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1))
% 52.22/52.46           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['340', '341', '342', '343'])).
% 52.22/52.46  thf('345', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 52.22/52.46           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.46      inference('demod', [status(thm)], ['326', '327'])).
% 52.22/52.46  thf('346', plain,
% 52.22/52.46      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['12', '13'])).
% 52.22/52.46  thf('347', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['96', '97'])).
% 52.22/52.46  thf('348', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ 
% 52.22/52.46           (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['346', '347'])).
% 52.22/52.46  thf('349', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['79', '84'])).
% 52.22/52.46  thf('350', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((X0)
% 52.22/52.46           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['348', '349'])).
% 52.22/52.46  thf('351', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 52.22/52.46           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['87', '88'])).
% 52.22/52.46  thf('352', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 52.22/52.46           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X2))
% 52.22/52.46           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['350', '351'])).
% 52.22/52.46  thf('353', plain,
% 52.22/52.46      (![X11 : $i, X12 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 52.22/52.46           = (k3_xboole_0 @ X11 @ X12))),
% 52.22/52.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 52.22/52.46  thf('354', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 52.22/52.46           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X2))
% 52.22/52.46           = (k3_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['352', '353'])).
% 52.22/52.46  thf('355', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['151', '152'])).
% 52.22/52.46  thf('356', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X1 @ X0)
% 52.22/52.46           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['207', '219'])).
% 52.22/52.46  thf('357', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X1 @ X0)
% 52.22/52.46           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['355', '356'])).
% 52.22/52.46  thf('358', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 52.22/52.46           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['222', '223', '224', '225', '226'])).
% 52.22/52.46  thf('359', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 52.22/52.46           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.46      inference('demod', [status(thm)], ['326', '327'])).
% 52.22/52.46  thf('360', plain,
% 52.22/52.46      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['12', '13'])).
% 52.22/52.46  thf('361', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.46              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 52.22/52.46      inference('sup+', [status(thm)], ['23', '24'])).
% 52.22/52.46  thf('362', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 52.22/52.46           = (k2_xboole_0 @ 
% 52.22/52.46              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.46              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))))),
% 52.22/52.46      inference('sup+', [status(thm)], ['360', '361'])).
% 52.22/52.46  thf('363', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['29', '30'])).
% 52.22/52.46  thf('364', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['60', '61'])).
% 52.22/52.46  thf('365', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 52.22/52.46           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['362', '363', '364'])).
% 52.22/52.46  thf('366', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['151', '152'])).
% 52.22/52.46  thf('367', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['151', '152'])).
% 52.22/52.46  thf('368', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 52.22/52.46      inference('demod', [status(thm)], ['365', '366', '367'])).
% 52.22/52.46  thf('369', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X1 @ X0)
% 52.22/52.46           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['207', '219'])).
% 52.22/52.46  thf('370', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['1', '2'])).
% 52.22/52.46  thf('371', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 52.22/52.46           (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))) = (X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['158', '159', '160'])).
% 52.22/52.46  thf('372', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ 
% 52.22/52.46           (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 52.22/52.46            (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))))
% 52.22/52.46           = (k3_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['370', '371'])).
% 52.22/52.46  thf('373', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['1', '2'])).
% 52.22/52.46  thf('374', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['29', '30'])).
% 52.22/52.46  thf('375', plain,
% 52.22/52.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.46  thf('376', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['16', '17'])).
% 52.22/52.46  thf('377', plain,
% 52.22/52.46      (![X4 : $i, X5 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X4 @ X5)
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 52.22/52.46      inference('cnf', [status(esa)], [d6_xboole_0])).
% 52.22/52.46  thf('378', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ 
% 52.22/52.46              (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 52.22/52.46      inference('sup+', [status(thm)], ['376', '377'])).
% 52.22/52.46  thf('379', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('380', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 52.22/52.46           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.46              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['378', '379'])).
% 52.22/52.46  thf('381', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['29', '30'])).
% 52.22/52.46  thf('382', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['201', '202'])).
% 52.22/52.46  thf('383', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 52.22/52.46              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['380', '381', '382'])).
% 52.22/52.46  thf('384', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 52.22/52.46           = (k5_xboole_0 @ X0 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['335', '336'])).
% 52.22/52.46  thf('385', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['79', '84'])).
% 52.22/52.46  thf('386', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k4_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['383', '384', '385'])).
% 52.22/52.46  thf('387', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k4_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['375', '386'])).
% 52.22/52.46  thf('388', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (k3_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['372', '373', '374', '387'])).
% 52.22/52.46  thf('389', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X1 @ X0)
% 52.22/52.46           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['207', '219'])).
% 52.22/52.46  thf('390', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X1 @ X0)
% 52.22/52.46           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['368', '369', '388', '389'])).
% 52.22/52.46  thf('391', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1))
% 52.22/52.46           = (k3_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['354', '357', '358', '359', '390'])).
% 52.22/52.46  thf('392', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['38', '76'])).
% 52.22/52.46  thf('393', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1) @ X0)
% 52.22/52.46           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['391', '392'])).
% 52.22/52.46  thf('394', plain,
% 52.22/52.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.46  thf('395', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['108', '113'])).
% 52.22/52.46  thf('396', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1))
% 52.22/52.46           = (k3_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['393', '394', '395'])).
% 52.22/52.46  thf('397', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 52.22/52.46           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 52.22/52.46      inference('demod', [status(thm)], ['326', '327'])).
% 52.22/52.46  thf('398', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 52.22/52.46           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['344', '345', '396', '397'])).
% 52.22/52.46  thf('399', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['201', '202'])).
% 52.22/52.46  thf('400', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('demod', [status(thm)],
% 52.22/52.46                ['295', '296', '297', '298', '299', '300', '301'])).
% 52.22/52.46  thf('401', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['60', '61'])).
% 52.22/52.46  thf('402', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['79', '84'])).
% 52.22/52.46  thf('403', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X1 @ X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['401', '402'])).
% 52.22/52.46  thf('404', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['253', '254'])).
% 52.22/52.46  thf('405', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 52.22/52.46              (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))))),
% 52.22/52.46      inference('demod', [status(thm)], ['123', '124'])).
% 52.22/52.46  thf('406', plain,
% 52.22/52.46      (![X0 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0))))),
% 52.22/52.46      inference('sup+', [status(thm)], ['404', '405'])).
% 52.22/52.46  thf('407', plain,
% 52.22/52.46      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['12', '13'])).
% 52.22/52.46  thf('408', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['10', '11'])).
% 52.22/52.46  thf('409', plain,
% 52.22/52.46      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['12', '13'])).
% 52.22/52.46  thf('410', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['79', '84'])).
% 52.22/52.46  thf('411', plain,
% 52.22/52.46      (![X0 : $i]: ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['406', '407', '408', '409', '410'])).
% 52.22/52.46  thf('412', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['403', '411'])).
% 52.22/52.46  thf('413', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['29', '30'])).
% 52.22/52.46  thf('414', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['412', '413'])).
% 52.22/52.46  thf('415', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('416', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['151', '152'])).
% 52.22/52.46  thf('417', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['415', '416'])).
% 52.22/52.46  thf('418', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X1 @ X0)
% 52.22/52.46           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['207', '219'])).
% 52.22/52.46  thf('419', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X1 @ X0)
% 52.22/52.46           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['417', '418'])).
% 52.22/52.46  thf('420', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 52.22/52.46           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['344', '345', '396', '397'])).
% 52.22/52.46  thf('421', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['201', '202'])).
% 52.22/52.46  thf('422', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['79', '84'])).
% 52.22/52.46  thf('423', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('424', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.46              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 52.22/52.46      inference('sup+', [status(thm)], ['23', '24'])).
% 52.22/52.46  thf('425', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.46              (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))))),
% 52.22/52.46      inference('sup+', [status(thm)], ['423', '424'])).
% 52.22/52.46  thf('426', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X1)) @ X0)
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 52.22/52.46              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X1)))))),
% 52.22/52.46      inference('sup+', [status(thm)], ['422', '425'])).
% 52.22/52.46  thf('427', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((X0) = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['70', '71'])).
% 52.22/52.46  thf('428', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((X0) = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['70', '71'])).
% 52.22/52.46  thf('429', plain,
% 52.22/52.46      (![X0 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X2 @ X0)
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 52.22/52.46      inference('demod', [status(thm)], ['426', '427', '428'])).
% 52.22/52.46  thf('430', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 52.22/52.46      inference('sup+', [status(thm)], ['50', '51'])).
% 52.22/52.46  thf('431', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.46              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 52.22/52.46      inference('demod', [status(thm)], ['319', '320'])).
% 52.22/52.46  thf('432', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 52.22/52.46              (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ (k4_xboole_0 @ X1 @ X0))))),
% 52.22/52.46      inference('sup+', [status(thm)], ['430', '431'])).
% 52.22/52.46  thf('433', plain,
% 52.22/52.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.46           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.46      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.46  thf('434', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['96', '97'])).
% 52.22/52.46  thf('435', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ (k4_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 52.22/52.46      inference('demod', [status(thm)], ['432', '433', '434'])).
% 52.22/52.46  thf('436', plain,
% 52.22/52.46      (![X0 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X2 @ X0)
% 52.22/52.46           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ (k4_xboole_0 @ X2 @ X0)))),
% 52.22/52.46      inference('demod', [status(thm)], ['429', '435'])).
% 52.22/52.46  thf('437', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)],
% 52.22/52.46                ['333', '398', '399', '400', '414', '419', '420', '421', '436'])).
% 52.22/52.46  thf('438', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('439', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X1 @ X0)
% 52.22/52.46           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['207', '219'])).
% 52.22/52.46  thf('440', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X1 @ X0)
% 52.22/52.46           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['438', '439'])).
% 52.22/52.46  thf('441', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['437', '440'])).
% 52.22/52.46  thf('442', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['144', '145'])).
% 52.22/52.46  thf('443', plain,
% 52.22/52.46      (![X4 : $i, X5 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X4 @ X5)
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 52.22/52.46      inference('cnf', [status(esa)], [d6_xboole_0])).
% 52.22/52.46  thf('444', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.46              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 52.22/52.46      inference('sup+', [status(thm)], ['23', '24'])).
% 52.22/52.46  thf('445', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.46           (k4_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.46              (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 52.22/52.46               (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))))),
% 52.22/52.46      inference('sup+', [status(thm)], ['443', '444'])).
% 52.22/52.46  thf('446', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['29', '30'])).
% 52.22/52.46  thf('447', plain,
% 52.22/52.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 52.22/52.46           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 52.22/52.46      inference('cnf', [status(esa)], [t41_xboole_1])).
% 52.22/52.46  thf('448', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 52.22/52.46           (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.46              (k4_xboole_0 @ X0 @ 
% 52.22/52.46               (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))))),
% 52.22/52.46      inference('demod', [status(thm)], ['445', '446', '447'])).
% 52.22/52.46  thf('449', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 52.22/52.46           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 52.22/52.46           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 52.22/52.46              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 52.22/52.46      inference('sup+', [status(thm)], ['442', '448'])).
% 52.22/52.46  thf('450', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['144', '145'])).
% 52.22/52.46  thf('451', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('sup+', [status(thm)], ['29', '30'])).
% 52.22/52.46  thf('452', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 52.22/52.46           = (k3_xboole_0 @ X1 @ X0))),
% 52.22/52.46      inference('demod', [status(thm)], ['372', '373', '374', '387'])).
% 52.22/52.46  thf('453', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k5_xboole_0 @ X0 @ X0)
% 52.22/52.46           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['138', '139'])).
% 52.22/52.46  thf('454', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 52.22/52.46  thf('455', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['60', '61'])).
% 52.22/52.46  thf('456', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X1 @ X0)
% 52.22/52.46           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('demod', [status(thm)],
% 52.22/52.46                ['449', '450', '451', '452', '453', '454', '455'])).
% 52.22/52.46  thf('457', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 52.22/52.46      inference('demod', [status(thm)], ['201', '202'])).
% 52.22/52.46  thf('458', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['456', '457'])).
% 52.22/52.46  thf('459', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('sup+', [status(thm)], ['108', '113'])).
% 52.22/52.46  thf('460', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 52.22/52.46           = (k3_xboole_0 @ X0 @ X1))),
% 52.22/52.46      inference('demod', [status(thm)], ['458', '459'])).
% 52.22/52.46  thf('461', plain,
% 52.22/52.46      (![X0 : $i, X1 : $i]:
% 52.22/52.46         ((k3_xboole_0 @ X0 @ X1)
% 52.22/52.46           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 52.22/52.46      inference('demod', [status(thm)], ['441', '460'])).
% 52.22/52.46  thf('462', plain,
% 52.22/52.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 52.22/52.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.22/52.46  thf('463', plain,
% 52.22/52.46      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 52.22/52.46      inference('demod', [status(thm)], ['0', '461', '462'])).
% 52.22/52.46  thf('464', plain, ($false), inference('simplify', [status(thm)], ['463'])).
% 52.22/52.46  
% 52.22/52.46  % SZS output end Refutation
% 52.22/52.46  
% 52.33/52.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
