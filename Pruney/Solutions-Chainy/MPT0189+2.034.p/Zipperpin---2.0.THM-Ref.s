%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PdcCQfQDpO

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:10 EST 2020

% Result     : Theorem 29.16s
% Output     : Refutation 29.16s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 128 expanded)
%              Number of leaves         :   18 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  727 (1290 expanded)
%              Number of equality atoms :   65 ( 117 expanded)
%              Maximal formula depth    :   14 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t108_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ B @ A @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t108_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X7 @ X10 @ X8 @ X9 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X0 @ X2 @ X1 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X3 @ X4 @ X6 @ X5 )
      = ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('11',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X7 @ X10 @ X8 @ X9 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('18',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('23',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X0 @ X1 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['9','16','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('47',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_enumset1 @ X2 @ X0 @ X1 @ X3 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X7 @ X10 @ X8 @ X9 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('53',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X3 @ X4 @ X6 @ X5 )
      = ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','51','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PdcCQfQDpO
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:35:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 29.16/29.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 29.16/29.37  % Solved by: fo/fo7.sh
% 29.16/29.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.16/29.37  % done 18104 iterations in 28.909s
% 29.16/29.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 29.16/29.37  % SZS output start Refutation
% 29.16/29.37  thf(sk_D_type, type, sk_D: $i).
% 29.16/29.37  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 29.16/29.37  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 29.16/29.37  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 29.16/29.37  thf(sk_B_type, type, sk_B: $i).
% 29.16/29.37  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 29.16/29.37  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 29.16/29.37  thf(sk_C_type, type, sk_C: $i).
% 29.16/29.37  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 29.16/29.37  thf(sk_A_type, type, sk_A: $i).
% 29.16/29.37  thf(t108_enumset1, conjecture,
% 29.16/29.37    (![A:$i,B:$i,C:$i,D:$i]:
% 29.16/29.37     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 29.16/29.37  thf(zf_stmt_0, negated_conjecture,
% 29.16/29.37    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 29.16/29.37        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 29.16/29.37    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 29.16/29.37  thf('0', plain,
% 29.16/29.37      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 29.16/29.37         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 29.16/29.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.16/29.37  thf(t105_enumset1, axiom,
% 29.16/29.37    (![A:$i,B:$i,C:$i,D:$i]:
% 29.16/29.37     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 29.16/29.37  thf('1', plain,
% 29.16/29.37      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X7 @ X10 @ X8 @ X9)
% 29.16/29.37           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 29.16/29.37      inference('cnf', [status(esa)], [t105_enumset1])).
% 29.16/29.37  thf(t71_enumset1, axiom,
% 29.16/29.37    (![A:$i,B:$i,C:$i]:
% 29.16/29.37     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 29.16/29.37  thf('2', plain,
% 29.16/29.37      (![X35 : $i, X36 : $i, X37 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 29.16/29.37           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 29.16/29.37      inference('cnf', [status(esa)], [t71_enumset1])).
% 29.16/29.37  thf('3', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 29.16/29.37      inference('sup+', [status(thm)], ['1', '2'])).
% 29.16/29.37  thf(t50_enumset1, axiom,
% 29.16/29.37    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 29.16/29.37     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 29.16/29.37       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 29.16/29.37  thf('4', plain,
% 29.16/29.37      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15)
% 29.16/29.37           = (k2_xboole_0 @ (k2_enumset1 @ X11 @ X12 @ X13 @ X14) @ 
% 29.16/29.37              (k1_tarski @ X15)))),
% 29.16/29.37      inference('cnf', [status(esa)], [t50_enumset1])).
% 29.16/29.37  thf('5', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X2 @ X0 @ X2 @ X1 @ X3)
% 29.16/29.37           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 29.16/29.37      inference('sup+', [status(thm)], ['3', '4'])).
% 29.16/29.37  thf(t72_enumset1, axiom,
% 29.16/29.37    (![A:$i,B:$i,C:$i,D:$i]:
% 29.16/29.37     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 29.16/29.37  thf('6', plain,
% 29.16/29.37      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 29.16/29.37           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 29.16/29.37      inference('cnf', [status(esa)], [t72_enumset1])).
% 29.16/29.37  thf('7', plain,
% 29.16/29.37      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15)
% 29.16/29.37           = (k2_xboole_0 @ (k2_enumset1 @ X11 @ X12 @ X13 @ X14) @ 
% 29.16/29.37              (k1_tarski @ X15)))),
% 29.16/29.37      inference('cnf', [status(esa)], [t50_enumset1])).
% 29.16/29.37  thf('8', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 29.16/29.37           = (k2_xboole_0 @ (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0) @ 
% 29.16/29.37              (k1_tarski @ X4)))),
% 29.16/29.37      inference('sup+', [status(thm)], ['6', '7'])).
% 29.16/29.37  thf('9', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X1 @ X1 @ X2 @ X0 @ X3)
% 29.16/29.37           = (k2_xboole_0 @ 
% 29.16/29.37              (k2_xboole_0 @ (k1_enumset1 @ X1 @ X2 @ X1) @ (k1_tarski @ X0)) @ 
% 29.16/29.37              (k1_tarski @ X3)))),
% 29.16/29.37      inference('sup+', [status(thm)], ['5', '8'])).
% 29.16/29.37  thf(t103_enumset1, axiom,
% 29.16/29.37    (![A:$i,B:$i,C:$i,D:$i]:
% 29.16/29.37     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 29.16/29.37  thf('10', plain,
% 29.16/29.37      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X3 @ X4 @ X6 @ X5) = (k2_enumset1 @ X3 @ X4 @ X5 @ X6))),
% 29.16/29.37      inference('cnf', [status(esa)], [t103_enumset1])).
% 29.16/29.37  thf('11', plain,
% 29.16/29.37      (![X35 : $i, X36 : $i, X37 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 29.16/29.37           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 29.16/29.37      inference('cnf', [status(esa)], [t71_enumset1])).
% 29.16/29.37  thf('12', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 29.16/29.37      inference('sup+', [status(thm)], ['10', '11'])).
% 29.16/29.37  thf('13', plain,
% 29.16/29.37      (![X35 : $i, X36 : $i, X37 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 29.16/29.37           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 29.16/29.37      inference('cnf', [status(esa)], [t71_enumset1])).
% 29.16/29.37  thf('14', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 29.16/29.37      inference('sup+', [status(thm)], ['12', '13'])).
% 29.16/29.37  thf(t70_enumset1, axiom,
% 29.16/29.37    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 29.16/29.37  thf('15', plain,
% 29.16/29.37      (![X33 : $i, X34 : $i]:
% 29.16/29.37         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 29.16/29.37      inference('cnf', [status(esa)], [t70_enumset1])).
% 29.16/29.37  thf('16', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i]:
% 29.16/29.37         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 29.16/29.37      inference('sup+', [status(thm)], ['14', '15'])).
% 29.16/29.37  thf('17', plain,
% 29.16/29.37      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X7 @ X10 @ X8 @ X9)
% 29.16/29.37           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 29.16/29.37      inference('cnf', [status(esa)], [t105_enumset1])).
% 29.16/29.37  thf('18', plain,
% 29.16/29.37      (![X35 : $i, X36 : $i, X37 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 29.16/29.37           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 29.16/29.37      inference('cnf', [status(esa)], [t71_enumset1])).
% 29.16/29.37  thf('19', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 29.16/29.37      inference('sup+', [status(thm)], ['17', '18'])).
% 29.16/29.37  thf('20', plain,
% 29.16/29.37      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 29.16/29.37           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 29.16/29.37      inference('cnf', [status(esa)], [t72_enumset1])).
% 29.16/29.37  thf('21', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 29.16/29.37      inference('sup+', [status(thm)], ['19', '20'])).
% 29.16/29.37  thf(t102_enumset1, axiom,
% 29.16/29.37    (![A:$i,B:$i,C:$i]:
% 29.16/29.37     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 29.16/29.37  thf('22', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 29.16/29.37      inference('cnf', [status(esa)], [t102_enumset1])).
% 29.16/29.37  thf('23', plain,
% 29.16/29.37      (![X33 : $i, X34 : $i]:
% 29.16/29.37         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 29.16/29.37      inference('cnf', [status(esa)], [t70_enumset1])).
% 29.16/29.37  thf('24', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i]:
% 29.16/29.37         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 29.16/29.37      inference('sup+', [status(thm)], ['22', '23'])).
% 29.16/29.37  thf('25', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 29.16/29.37      inference('sup+', [status(thm)], ['10', '11'])).
% 29.16/29.37  thf('26', plain,
% 29.16/29.37      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15)
% 29.16/29.37           = (k2_xboole_0 @ (k2_enumset1 @ X11 @ X12 @ X13 @ X14) @ 
% 29.16/29.37              (k1_tarski @ X15)))),
% 29.16/29.37      inference('cnf', [status(esa)], [t50_enumset1])).
% 29.16/29.37  thf('27', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X2 @ X2 @ X0 @ X1 @ X3)
% 29.16/29.37           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 29.16/29.37      inference('sup+', [status(thm)], ['25', '26'])).
% 29.16/29.37  thf('28', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X0 @ X0 @ X1 @ X1 @ X2)
% 29.16/29.37           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 29.16/29.37      inference('sup+', [status(thm)], ['24', '27'])).
% 29.16/29.37  thf('29', plain,
% 29.16/29.37      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 29.16/29.37           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 29.16/29.37      inference('cnf', [status(esa)], [t72_enumset1])).
% 29.16/29.37  thf('30', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 29.16/29.37      inference('sup+', [status(thm)], ['10', '11'])).
% 29.16/29.37  thf('31', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 29.16/29.37      inference('sup+', [status(thm)], ['29', '30'])).
% 29.16/29.37  thf('32', plain,
% 29.16/29.37      (![X35 : $i, X36 : $i, X37 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 29.16/29.37           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 29.16/29.37      inference('cnf', [status(esa)], [t71_enumset1])).
% 29.16/29.37  thf('33', plain,
% 29.16/29.37      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15)
% 29.16/29.37           = (k2_xboole_0 @ (k2_enumset1 @ X11 @ X12 @ X13 @ X14) @ 
% 29.16/29.37              (k1_tarski @ X15)))),
% 29.16/29.37      inference('cnf', [status(esa)], [t50_enumset1])).
% 29.16/29.37  thf('34', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 29.16/29.37           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 29.16/29.37      inference('sup+', [status(thm)], ['32', '33'])).
% 29.16/29.37  thf('35', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k1_enumset1 @ X2 @ X1 @ X0)
% 29.16/29.37           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X0) @ (k1_tarski @ X1)))),
% 29.16/29.37      inference('sup+', [status(thm)], ['31', '34'])).
% 29.16/29.37  thf('36', plain,
% 29.16/29.37      (![X33 : $i, X34 : $i]:
% 29.16/29.37         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 29.16/29.37      inference('cnf', [status(esa)], [t70_enumset1])).
% 29.16/29.37  thf('37', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k1_enumset1 @ X2 @ X1 @ X0)
% 29.16/29.37           = (k2_xboole_0 @ (k2_tarski @ X2 @ X0) @ (k1_tarski @ X1)))),
% 29.16/29.37      inference('demod', [status(thm)], ['35', '36'])).
% 29.16/29.37  thf('38', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X0 @ X0 @ X1 @ X1 @ X2) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 29.16/29.37      inference('demod', [status(thm)], ['28', '37'])).
% 29.16/29.37  thf('39', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i]:
% 29.16/29.37         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 29.16/29.37      inference('sup+', [status(thm)], ['21', '38'])).
% 29.16/29.37  thf('40', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i]:
% 29.16/29.37         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 29.16/29.37      inference('sup+', [status(thm)], ['22', '23'])).
% 29.16/29.37  thf('41', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i]:
% 29.16/29.37         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 29.16/29.37      inference('sup+', [status(thm)], ['22', '23'])).
% 29.16/29.37  thf('42', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 29.16/29.37      inference('demod', [status(thm)], ['39', '40', '41'])).
% 29.16/29.37  thf('43', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k1_enumset1 @ X2 @ X1 @ X0)
% 29.16/29.37           = (k2_xboole_0 @ (k2_tarski @ X2 @ X0) @ (k1_tarski @ X1)))),
% 29.16/29.37      inference('demod', [status(thm)], ['35', '36'])).
% 29.16/29.37  thf('44', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.16/29.37         ((k1_enumset1 @ X0 @ X2 @ X1)
% 29.16/29.37           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 29.16/29.37      inference('sup+', [status(thm)], ['42', '43'])).
% 29.16/29.37  thf('45', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X1 @ X1 @ X2 @ X0 @ X3)
% 29.16/29.37           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X0 @ X1) @ (k1_tarski @ X3)))),
% 29.16/29.37      inference('demod', [status(thm)], ['9', '16', '44'])).
% 29.16/29.37  thf('46', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 29.16/29.37           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 29.16/29.37      inference('sup+', [status(thm)], ['32', '33'])).
% 29.16/29.37  thf('47', plain,
% 29.16/29.37      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 29.16/29.37           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 29.16/29.37      inference('cnf', [status(esa)], [t72_enumset1])).
% 29.16/29.37  thf('48', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.16/29.37         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 29.16/29.37           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 29.16/29.37      inference('sup+', [status(thm)], ['46', '47'])).
% 29.16/29.37  thf('49', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X1 @ X1 @ X2 @ X0 @ X3)
% 29.16/29.37           = (k2_enumset1 @ X2 @ X0 @ X1 @ X3))),
% 29.16/29.37      inference('demod', [status(thm)], ['45', '48'])).
% 29.16/29.37  thf('50', plain,
% 29.16/29.37      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 29.16/29.37         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 29.16/29.37           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 29.16/29.37      inference('cnf', [status(esa)], [t72_enumset1])).
% 29.16/29.37  thf('51', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X3 @ X2 @ X0))),
% 29.16/29.37      inference('sup+', [status(thm)], ['49', '50'])).
% 29.16/29.37  thf('52', plain,
% 29.16/29.37      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X7 @ X10 @ X8 @ X9)
% 29.16/29.37           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 29.16/29.37      inference('cnf', [status(esa)], [t105_enumset1])).
% 29.16/29.37  thf('53', plain,
% 29.16/29.37      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X3 @ X4 @ X6 @ X5) = (k2_enumset1 @ X3 @ X4 @ X5 @ X6))),
% 29.16/29.37      inference('cnf', [status(esa)], [t103_enumset1])).
% 29.16/29.37  thf('54', plain,
% 29.16/29.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.16/29.37         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 29.16/29.37      inference('sup+', [status(thm)], ['52', '53'])).
% 29.16/29.37  thf('55', plain,
% 29.16/29.37      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 29.16/29.37         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 29.16/29.37      inference('demod', [status(thm)], ['0', '51', '54'])).
% 29.16/29.37  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 29.16/29.37  
% 29.16/29.37  % SZS output end Refutation
% 29.16/29.37  
% 29.16/29.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
