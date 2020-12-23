%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XqTsd2iwsw

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:17 EST 2020

% Result     : Theorem 11.12s
% Output     : Refutation 11.12s
% Verified   : 
% Statistics : Number of formulae       :  169 (12477 expanded)
%              Number of leaves         :   12 (4390 expanded)
%              Depth                    :   28
%              Number of atoms          : 1759 (125347 expanded)
%              Number of equality atoms :  162 (12470 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t49_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
        = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t49_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('44',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37','40','41','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('58',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['49','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','77'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('111',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['109','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','108'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['91','94','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','108'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['91','94','133'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['65','134','135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['65','134','135','136'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','108'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','108'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['147','148','149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','146','153'])).

thf('155',plain,(
    $false ),
    inference(simplify,[status(thm)],['154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XqTsd2iwsw
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:54:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 11.12/11.30  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.12/11.30  % Solved by: fo/fo7.sh
% 11.12/11.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.12/11.30  % done 4284 iterations in 10.851s
% 11.12/11.30  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.12/11.30  % SZS output start Refutation
% 11.12/11.30  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 11.12/11.30  thf(sk_C_type, type, sk_C: $i).
% 11.12/11.30  thf(sk_B_type, type, sk_B: $i).
% 11.12/11.30  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 11.12/11.30  thf(sk_A_type, type, sk_A: $i).
% 11.12/11.30  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 11.12/11.30  thf(t49_xboole_1, conjecture,
% 11.12/11.30    (![A:$i,B:$i,C:$i]:
% 11.12/11.30     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 11.12/11.30       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 11.12/11.30  thf(zf_stmt_0, negated_conjecture,
% 11.12/11.30    (~( ![A:$i,B:$i,C:$i]:
% 11.12/11.30        ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 11.12/11.30          ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )),
% 11.12/11.30    inference('cnf.neg', [status(esa)], [t49_xboole_1])).
% 11.12/11.30  thf('0', plain,
% 11.12/11.30      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 11.12/11.30         != (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 11.12/11.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.12/11.30  thf(t48_xboole_1, axiom,
% 11.12/11.30    (![A:$i,B:$i]:
% 11.12/11.30     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 11.12/11.30  thf('1', plain,
% 11.12/11.30      (![X9 : $i, X10 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.30           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.30  thf('2', plain,
% 11.12/11.30      (![X9 : $i, X10 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.30           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.30  thf('3', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 11.12/11.30      inference('sup+', [status(thm)], ['1', '2'])).
% 11.12/11.30  thf(t47_xboole_1, axiom,
% 11.12/11.30    (![A:$i,B:$i]:
% 11.12/11.30     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 11.12/11.30  thf('4', plain,
% 11.12/11.30      (![X7 : $i, X8 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 11.12/11.30           = (k4_xboole_0 @ X7 @ X8))),
% 11.12/11.30      inference('cnf', [status(esa)], [t47_xboole_1])).
% 11.12/11.30  thf('5', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k4_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('sup+', [status(thm)], ['3', '4'])).
% 11.12/11.30  thf(t41_xboole_1, axiom,
% 11.12/11.30    (![A:$i,B:$i,C:$i]:
% 11.12/11.30     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 11.12/11.30       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 11.12/11.30  thf('6', plain,
% 11.12/11.30      (![X4 : $i, X5 : $i, X6 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 11.12/11.30           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 11.12/11.30      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.12/11.30  thf(t39_xboole_1, axiom,
% 11.12/11.30    (![A:$i,B:$i]:
% 11.12/11.30     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 11.12/11.30  thf('7', plain,
% 11.12/11.30      (![X2 : $i, X3 : $i]:
% 11.12/11.30         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 11.12/11.30           = (k2_xboole_0 @ X2 @ X3))),
% 11.12/11.30      inference('cnf', [status(esa)], [t39_xboole_1])).
% 11.12/11.30  thf('8', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 11.12/11.30           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 11.12/11.30      inference('sup+', [status(thm)], ['6', '7'])).
% 11.12/11.30  thf('9', plain,
% 11.12/11.30      (![X9 : $i, X10 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.30           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.30  thf('10', plain,
% 11.12/11.30      (![X4 : $i, X5 : $i, X6 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 11.12/11.30           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 11.12/11.30      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.12/11.30  thf('11', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 11.12/11.30           = (k4_xboole_0 @ X2 @ 
% 11.12/11.30              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 11.12/11.30      inference('sup+', [status(thm)], ['9', '10'])).
% 11.12/11.30  thf('12', plain,
% 11.12/11.30      (![X4 : $i, X5 : $i, X6 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 11.12/11.30           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 11.12/11.30      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.12/11.30  thf('13', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 11.12/11.30           = (k4_xboole_0 @ X2 @ 
% 11.12/11.30              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 11.12/11.30      inference('demod', [status(thm)], ['11', '12'])).
% 11.12/11.30  thf('14', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 11.12/11.30           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 11.12/11.30      inference('sup+', [status(thm)], ['8', '13'])).
% 11.12/11.30  thf(commutativity_k3_xboole_0, axiom,
% 11.12/11.30    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 11.12/11.30  thf('15', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.12/11.30  thf('16', plain,
% 11.12/11.30      (![X2 : $i, X3 : $i]:
% 11.12/11.30         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 11.12/11.30           = (k2_xboole_0 @ X2 @ X3))),
% 11.12/11.30      inference('cnf', [status(esa)], [t39_xboole_1])).
% 11.12/11.30  thf('17', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 11.12/11.30      inference('demod', [status(thm)], ['14', '15', '16'])).
% 11.12/11.30  thf('18', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.12/11.30  thf('19', plain,
% 11.12/11.30      (![X7 : $i, X8 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 11.12/11.30           = (k4_xboole_0 @ X7 @ X8))),
% 11.12/11.30      inference('cnf', [status(esa)], [t47_xboole_1])).
% 11.12/11.30  thf('20', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k4_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('sup+', [status(thm)], ['18', '19'])).
% 11.12/11.30  thf('21', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 11.12/11.30           (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 11.12/11.30           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 11.12/11.30      inference('sup+', [status(thm)], ['17', '20'])).
% 11.12/11.30  thf('22', plain,
% 11.12/11.30      (![X4 : $i, X5 : $i, X6 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 11.12/11.30           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 11.12/11.30      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.12/11.30  thf('23', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 11.12/11.30           = (k4_xboole_0 @ X2 @ 
% 11.12/11.30              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 11.12/11.30      inference('demod', [status(thm)], ['11', '12'])).
% 11.12/11.30  thf('24', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.12/11.30  thf('25', plain,
% 11.12/11.30      (![X4 : $i, X5 : $i, X6 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 11.12/11.30           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 11.12/11.30      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.12/11.30  thf('26', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 11.12/11.30           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 11.12/11.30      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 11.12/11.30  thf('27', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k4_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('sup+', [status(thm)], ['3', '4'])).
% 11.12/11.30  thf('28', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X0 @ X1)
% 11.12/11.30           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 11.12/11.30      inference('demod', [status(thm)], ['26', '27'])).
% 11.12/11.30  thf('29', plain,
% 11.12/11.30      (![X9 : $i, X10 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.30           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.30  thf('30', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 11.12/11.30      inference('sup+', [status(thm)], ['28', '29'])).
% 11.12/11.30  thf('31', plain,
% 11.12/11.30      (![X9 : $i, X10 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.30           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.30  thf('32', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X1 @ X0)
% 11.12/11.30           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 11.12/11.30      inference('demod', [status(thm)], ['30', '31'])).
% 11.12/11.30  thf('33', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k4_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('sup+', [status(thm)], ['18', '19'])).
% 11.12/11.30  thf('34', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1))),
% 11.12/11.30      inference('sup+', [status(thm)], ['32', '33'])).
% 11.12/11.30  thf('35', plain,
% 11.12/11.30      (![X9 : $i, X10 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.30           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.30  thf('36', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ 
% 11.12/11.30           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0))
% 11.12/11.30           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 11.12/11.30      inference('sup+', [status(thm)], ['34', '35'])).
% 11.12/11.30  thf('37', plain,
% 11.12/11.30      (![X9 : $i, X10 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.30           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.30  thf('38', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X1 @ X0)
% 11.12/11.30           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 11.12/11.30      inference('demod', [status(thm)], ['30', '31'])).
% 11.12/11.30  thf('39', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.12/11.30  thf('40', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 11.12/11.30           = (k3_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.12/11.30  thf('41', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.12/11.30  thf('42', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.12/11.30  thf('43', plain,
% 11.12/11.30      (![X7 : $i, X8 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 11.12/11.30           = (k4_xboole_0 @ X7 @ X8))),
% 11.12/11.30      inference('cnf', [status(esa)], [t47_xboole_1])).
% 11.12/11.30  thf('44', plain,
% 11.12/11.30      (![X9 : $i, X10 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.30           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.30  thf('45', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 11.12/11.30      inference('sup+', [status(thm)], ['43', '44'])).
% 11.12/11.30  thf('46', plain,
% 11.12/11.30      (![X9 : $i, X10 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.30           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.30  thf('47', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k3_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('sup+', [status(thm)], ['45', '46'])).
% 11.12/11.30  thf('48', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('sup+', [status(thm)], ['42', '47'])).
% 11.12/11.30  thf('49', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0)
% 11.12/11.30           = (k3_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('demod', [status(thm)], ['36', '37', '40', '41', '48'])).
% 11.12/11.30  thf('50', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 11.12/11.30           = (k4_xboole_0 @ X2 @ 
% 11.12/11.30              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 11.12/11.30      inference('demod', [status(thm)], ['11', '12'])).
% 11.12/11.30  thf('51', plain,
% 11.12/11.30      (![X9 : $i, X10 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.30           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.30  thf('52', plain,
% 11.12/11.30      (![X4 : $i, X5 : $i, X6 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 11.12/11.30           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 11.12/11.30      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.12/11.30  thf('53', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 11.12/11.30           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 11.12/11.30      inference('sup+', [status(thm)], ['51', '52'])).
% 11.12/11.30  thf('54', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k4_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('sup+', [status(thm)], ['3', '4'])).
% 11.12/11.30  thf('55', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 11.12/11.30           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 11.12/11.30      inference('sup+', [status(thm)], ['53', '54'])).
% 11.12/11.30  thf('56', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X2 @ 
% 11.12/11.30           (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 11.12/11.30            (k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))
% 11.12/11.30           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X1)) @ X0))),
% 11.12/11.30      inference('sup+', [status(thm)], ['50', '55'])).
% 11.12/11.30  thf('57', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 11.12/11.30           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 11.12/11.30      inference('sup+', [status(thm)], ['51', '52'])).
% 11.12/11.30  thf('58', plain,
% 11.12/11.30      (![X9 : $i, X10 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.30           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.30  thf('59', plain,
% 11.12/11.30      (![X9 : $i, X10 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.30           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.30  thf('60', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 11.12/11.30           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 11.12/11.30      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 11.12/11.30  thf('61', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ 
% 11.12/11.30           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 11.12/11.30           = (k3_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0) @ X2))),
% 11.12/11.30      inference('sup+', [status(thm)], ['49', '60'])).
% 11.12/11.30  thf('62', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 11.12/11.30           = (k3_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.12/11.30  thf('63', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.12/11.30  thf('64', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 11.12/11.30           = (k3_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.12/11.30  thf('65', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 11.12/11.30           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 11.12/11.30      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 11.12/11.30  thf('66', plain,
% 11.12/11.30      (![X2 : $i, X3 : $i]:
% 11.12/11.30         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 11.12/11.30           = (k2_xboole_0 @ X2 @ X3))),
% 11.12/11.30      inference('cnf', [status(esa)], [t39_xboole_1])).
% 11.12/11.30  thf('67', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 11.12/11.30           = (k4_xboole_0 @ X2 @ 
% 11.12/11.30              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 11.12/11.30      inference('demod', [status(thm)], ['11', '12'])).
% 11.12/11.30  thf('68', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 11.12/11.30           = (k4_xboole_0 @ X2 @ 
% 11.12/11.30              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 11.12/11.30      inference('sup+', [status(thm)], ['66', '67'])).
% 11.12/11.30  thf('69', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 11.12/11.30           = (k4_xboole_0 @ X2 @ 
% 11.12/11.30              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 11.12/11.30      inference('demod', [status(thm)], ['11', '12'])).
% 11.12/11.30  thf('70', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 11.12/11.30           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 11.12/11.30      inference('sup+', [status(thm)], ['68', '69'])).
% 11.12/11.30  thf('71', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.12/11.30  thf('72', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('sup+', [status(thm)], ['42', '47'])).
% 11.12/11.30  thf('73', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('sup+', [status(thm)], ['42', '47'])).
% 11.12/11.30  thf('74', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1))),
% 11.12/11.30      inference('sup+', [status(thm)], ['72', '73'])).
% 11.12/11.30  thf('75', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.12/11.30  thf('76', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('sup+', [status(thm)], ['42', '47'])).
% 11.12/11.30  thf('77', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k3_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('demod', [status(thm)], ['74', '75', '76'])).
% 11.12/11.30  thf('78', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('sup+', [status(thm)], ['71', '77'])).
% 11.12/11.30  thf('79', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ 
% 11.12/11.30           (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1)) @ 
% 11.12/11.30           (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 11.12/11.30           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X1)))),
% 11.12/11.30      inference('sup+', [status(thm)], ['70', '78'])).
% 11.12/11.30  thf('80', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 11.12/11.30           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 11.12/11.30      inference('sup+', [status(thm)], ['68', '69'])).
% 11.12/11.30  thf('81', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('sup+', [status(thm)], ['71', '77'])).
% 11.12/11.30  thf('82', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 11.12/11.30           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 11.12/11.30      inference('sup+', [status(thm)], ['68', '69'])).
% 11.12/11.30  thf('83', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 11.12/11.30           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 11.12/11.30      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 11.12/11.30  thf('84', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k4_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('sup+', [status(thm)], ['18', '19'])).
% 11.12/11.30  thf('85', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 11.12/11.30           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0)))),
% 11.12/11.30      inference('sup+', [status(thm)], ['83', '84'])).
% 11.12/11.30  thf('86', plain,
% 11.12/11.30      (![X7 : $i, X8 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 11.12/11.30           = (k4_xboole_0 @ X7 @ X8))),
% 11.12/11.30      inference('cnf', [status(esa)], [t47_xboole_1])).
% 11.12/11.30  thf('87', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 11.12/11.30           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 11.12/11.30      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 11.12/11.30  thf('88', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 11.12/11.30           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 11.12/11.30      inference('sup+', [status(thm)], ['86', '87'])).
% 11.12/11.30  thf('89', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 11.12/11.30           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 11.12/11.30      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 11.12/11.30  thf('90', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 11.12/11.30           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0)))),
% 11.12/11.30      inference('demod', [status(thm)], ['88', '89'])).
% 11.12/11.30  thf('91', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 11.12/11.30           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X0))))),
% 11.12/11.30      inference('sup+', [status(thm)], ['85', '90'])).
% 11.12/11.30  thf('92', plain,
% 11.12/11.30      (![X9 : $i, X10 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.30           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.30  thf('93', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 11.12/11.30           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 11.12/11.30      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 11.12/11.30  thf('94', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 11.12/11.30           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 11.12/11.30      inference('sup+', [status(thm)], ['92', '93'])).
% 11.12/11.30  thf('95', plain,
% 11.12/11.30      (![X9 : $i, X10 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.30           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.30      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.30  thf('96', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k4_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('sup+', [status(thm)], ['3', '4'])).
% 11.12/11.30  thf('97', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 11.12/11.30           = (k3_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.12/11.30  thf('98', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0)
% 11.12/11.30           = (k3_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0) @ X1))),
% 11.12/11.30      inference('sup+', [status(thm)], ['96', '97'])).
% 11.12/11.30  thf('99', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.12/11.30  thf('100', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0)
% 11.12/11.30           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0)))),
% 11.12/11.30      inference('demod', [status(thm)], ['98', '99'])).
% 11.12/11.30  thf('101', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.12/11.30  thf('102', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 11.12/11.30           = (k3_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('sup+', [status(thm)], ['45', '46'])).
% 11.12/11.30  thf('103', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 11.12/11.30           = (k3_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.12/11.30  thf('104', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0)
% 11.12/11.30           = (k3_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0) @ X1))),
% 11.12/11.30      inference('sup+', [status(thm)], ['102', '103'])).
% 11.12/11.30  thf('105', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 11.12/11.30           = (k3_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.12/11.30  thf('106', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 11.12/11.30           = (k3_xboole_0 @ X1 @ X0))),
% 11.12/11.30      inference('sup+', [status(thm)], ['38', '39'])).
% 11.12/11.30  thf('107', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.12/11.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.12/11.30  thf('108', plain,
% 11.12/11.30      (![X0 : $i, X1 : $i]:
% 11.12/11.30         ((k3_xboole_0 @ X0 @ X1)
% 11.12/11.30           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 11.12/11.30      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 11.12/11.31  thf('109', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ X1)
% 11.12/11.31           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 11.12/11.31      inference('sup+', [status(thm)], ['101', '108'])).
% 11.12/11.31  thf('110', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 11.12/11.31           = (k4_xboole_0 @ X2 @ 
% 11.12/11.31              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 11.12/11.31      inference('demod', [status(thm)], ['11', '12'])).
% 11.12/11.31  thf('111', plain,
% 11.12/11.31      (![X9 : $i, X10 : $i]:
% 11.12/11.31         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.31           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.31  thf('112', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 11.12/11.31           = (k3_xboole_0 @ X2 @ 
% 11.12/11.31              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 11.12/11.31      inference('sup+', [status(thm)], ['110', '111'])).
% 11.12/11.31  thf('113', plain,
% 11.12/11.31      (![X7 : $i, X8 : $i]:
% 11.12/11.31         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 11.12/11.31           = (k4_xboole_0 @ X7 @ X8))),
% 11.12/11.31      inference('cnf', [status(esa)], [t47_xboole_1])).
% 11.12/11.31  thf('114', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k4_xboole_0 @ X2 @ 
% 11.12/11.31           (k4_xboole_0 @ X2 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 11.12/11.31           = (k4_xboole_0 @ X2 @ 
% 11.12/11.31              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 11.12/11.31      inference('sup+', [status(thm)], ['112', '113'])).
% 11.12/11.31  thf('115', plain,
% 11.12/11.31      (![X9 : $i, X10 : $i]:
% 11.12/11.31         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.12/11.31           = (k3_xboole_0 @ X9 @ X10))),
% 11.12/11.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.12/11.31  thf('116', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 11.12/11.31           = (k4_xboole_0 @ X2 @ 
% 11.12/11.31              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 11.12/11.31      inference('demod', [status(thm)], ['11', '12'])).
% 11.12/11.31  thf('117', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 11.12/11.31           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 11.12/11.31      inference('demod', [status(thm)], ['114', '115', '116'])).
% 11.12/11.31  thf('118', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 11.12/11.31           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 11.12/11.31              (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 11.12/11.31      inference('sup+', [status(thm)], ['109', '117'])).
% 11.12/11.31  thf('119', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ X1)
% 11.12/11.31           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 11.12/11.31      inference('sup+', [status(thm)], ['101', '108'])).
% 11.12/11.31  thf('120', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 11.12/11.31           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 11.12/11.31      inference('demod', [status(thm)], ['118', '119'])).
% 11.12/11.31  thf('121', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ 
% 11.12/11.31           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0))
% 11.12/11.31           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0)))),
% 11.12/11.31      inference('sup+', [status(thm)], ['100', '120'])).
% 11.12/11.31  thf('122', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 11.12/11.31           = (k3_xboole_0 @ X1 @ X0))),
% 11.12/11.31      inference('sup+', [status(thm)], ['38', '39'])).
% 11.12/11.31  thf('123', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 11.12/11.31           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 11.12/11.31      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 11.12/11.31  thf('124', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 11.12/11.31           = (k3_xboole_0 @ X1 @ X0))),
% 11.12/11.31      inference('sup+', [status(thm)], ['38', '39'])).
% 11.12/11.31  thf('125', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 11.12/11.31           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 11.12/11.31      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 11.12/11.31  thf('126', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0)
% 11.12/11.31           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0)))),
% 11.12/11.31      inference('demod', [status(thm)], ['98', '99'])).
% 11.12/11.31  thf('127', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 11.12/11.31           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0))),
% 11.12/11.31      inference('demod', [status(thm)],
% 11.12/11.31                ['121', '122', '123', '124', '125', '126'])).
% 11.12/11.31  thf('128', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 11.12/11.31           = (k4_xboole_0 @ X1 @ X0))),
% 11.12/11.31      inference('sup+', [status(thm)], ['3', '4'])).
% 11.12/11.31  thf('129', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0)
% 11.12/11.31           = (k4_xboole_0 @ X1 @ X0))),
% 11.12/11.31      inference('sup+', [status(thm)], ['127', '128'])).
% 11.12/11.31  thf('130', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0)
% 11.12/11.31           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0)))),
% 11.12/11.31      inference('sup+', [status(thm)], ['95', '129'])).
% 11.12/11.31  thf('131', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 11.12/11.31           = (k3_xboole_0 @ X1 @ X0))),
% 11.12/11.31      inference('sup+', [status(thm)], ['38', '39'])).
% 11.12/11.31  thf('132', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0)
% 11.12/11.31           = (k4_xboole_0 @ X1 @ X0))),
% 11.12/11.31      inference('sup+', [status(thm)], ['127', '128'])).
% 11.12/11.31  thf('133', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ X1)
% 11.12/11.31           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 11.12/11.31      inference('demod', [status(thm)], ['130', '131', '132'])).
% 11.12/11.31  thf('134', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 11.12/11.31           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2)))),
% 11.12/11.31      inference('demod', [status(thm)], ['91', '94', '133'])).
% 11.12/11.31  thf('135', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ X1)
% 11.12/11.31           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 11.12/11.31      inference('sup+', [status(thm)], ['101', '108'])).
% 11.12/11.31  thf('136', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 11.12/11.31           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2)))),
% 11.12/11.31      inference('demod', [status(thm)], ['91', '94', '133'])).
% 11.12/11.31  thf('137', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1)
% 11.12/11.31           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 11.12/11.31      inference('demod', [status(thm)], ['65', '134', '135', '136'])).
% 11.12/11.31  thf('138', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 11.12/11.31           = (k3_xboole_0 @ X2 @ 
% 11.12/11.31              (k3_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ X1)))),
% 11.12/11.31      inference('sup+', [status(thm)], ['5', '137'])).
% 11.12/11.31  thf('139', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 11.12/11.31           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 11.12/11.31      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 11.12/11.31  thf('140', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1)
% 11.12/11.31           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 11.12/11.31      inference('demod', [status(thm)], ['65', '134', '135', '136'])).
% 11.12/11.31  thf('141', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 11.12/11.31           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 11.12/11.31      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 11.12/11.31  thf('142', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 11.12/11.31           = (k4_xboole_0 @ X1 @ X0))),
% 11.12/11.31      inference('sup+', [status(thm)], ['3', '4'])).
% 11.12/11.31  thf('143', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ X1)
% 11.12/11.31           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 11.12/11.31      inference('sup+', [status(thm)], ['101', '108'])).
% 11.12/11.31  thf('144', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 11.12/11.31           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 11.12/11.31      inference('demod', [status(thm)],
% 11.12/11.31                ['138', '139', '140', '141', '142', '143'])).
% 11.12/11.31  thf('145', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 11.12/11.31           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 11.12/11.31      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 11.12/11.31  thf('146', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 11.12/11.31           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0)))),
% 11.12/11.31      inference('demod', [status(thm)], ['144', '145'])).
% 11.12/11.31  thf('147', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 11.12/11.31           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 11.12/11.31      inference('demod', [status(thm)], ['114', '115', '116'])).
% 11.12/11.31  thf('148', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 11.12/11.31           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 11.12/11.31      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 11.12/11.31  thf('149', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ X1)
% 11.12/11.31           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 11.12/11.31      inference('sup+', [status(thm)], ['101', '108'])).
% 11.12/11.31  thf('150', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 11.12/11.31           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 11.12/11.31      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 11.12/11.31  thf('151', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 11.12/11.31           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 11.12/11.31      inference('demod', [status(thm)], ['147', '148', '149', '150'])).
% 11.12/11.31  thf('152', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 11.12/11.31           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 11.12/11.31      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 11.12/11.31  thf('153', plain,
% 11.12/11.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.12/11.31         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 11.12/11.31           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 11.12/11.31      inference('demod', [status(thm)], ['151', '152'])).
% 11.12/11.31  thf('154', plain,
% 11.12/11.31      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 11.12/11.31         != (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 11.12/11.31      inference('demod', [status(thm)], ['0', '146', '153'])).
% 11.12/11.31  thf('155', plain, ($false), inference('simplify', [status(thm)], ['154'])).
% 11.12/11.31  
% 11.12/11.31  % SZS output end Refutation
% 11.12/11.31  
% 11.12/11.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
