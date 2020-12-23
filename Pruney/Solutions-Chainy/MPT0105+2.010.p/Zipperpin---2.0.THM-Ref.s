%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eKP26rfpDL

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:06 EST 2020

% Result     : Theorem 2.75s
% Output     : Refutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 221 expanded)
%              Number of leaves         :   19 (  83 expanded)
%              Depth                    :   16
%              Number of atoms          :  780 (1773 expanded)
%              Number of equality atoms :   83 ( 206 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t98_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t98_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ X5 @ X6 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ X5 @ X6 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('46',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('47',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('58',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','47','48','53','54','55','56','57','58'])).

thf('60',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('61',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('67',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','73'])).

thf('75',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','74'])).

thf('76',plain,(
    $false ),
    inference(simplify,[status(thm)],['75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eKP26rfpDL
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:01:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.75/2.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.75/2.99  % Solved by: fo/fo7.sh
% 2.75/2.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.75/2.99  % done 4248 iterations in 2.528s
% 2.75/2.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.75/2.99  % SZS output start Refutation
% 2.75/2.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.75/2.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.75/2.99  thf(sk_A_type, type, sk_A: $i).
% 2.75/2.99  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.75/2.99  thf(sk_B_type, type, sk_B: $i).
% 2.75/2.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.75/2.99  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.75/2.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.75/2.99  thf(t98_xboole_1, conjecture,
% 2.75/2.99    (![A:$i,B:$i]:
% 2.75/2.99     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.75/2.99  thf(zf_stmt_0, negated_conjecture,
% 2.75/2.99    (~( ![A:$i,B:$i]:
% 2.75/2.99        ( ( k2_xboole_0 @ A @ B ) =
% 2.75/2.99          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 2.75/2.99    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 2.75/2.99  thf('0', plain,
% 2.75/2.99      (((k2_xboole_0 @ sk_A @ sk_B)
% 2.75/2.99         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 2.75/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.75/2.99  thf(t79_xboole_1, axiom,
% 2.75/2.99    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 2.75/2.99  thf('1', plain,
% 2.75/2.99      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 2.75/2.99      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.75/2.99  thf(t83_xboole_1, axiom,
% 2.75/2.99    (![A:$i,B:$i]:
% 2.75/2.99     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.75/2.99  thf('2', plain,
% 2.75/2.99      (![X15 : $i, X16 : $i]:
% 2.75/2.99         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 2.75/2.99      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.75/2.99  thf('3', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]:
% 2.75/2.99         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 2.75/2.99           = (k4_xboole_0 @ X1 @ X0))),
% 2.75/2.99      inference('sup-', [status(thm)], ['1', '2'])).
% 2.75/2.99  thf(t48_xboole_1, axiom,
% 2.75/2.99    (![A:$i,B:$i]:
% 2.75/2.99     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.75/2.99  thf('4', plain,
% 2.75/2.99      (![X11 : $i, X12 : $i]:
% 2.75/2.99         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 2.75/2.99           = (k3_xboole_0 @ X11 @ X12))),
% 2.75/2.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.75/2.99  thf('5', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]:
% 2.75/2.99         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.75/2.99           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 2.75/2.99      inference('sup+', [status(thm)], ['3', '4'])).
% 2.75/2.99  thf(commutativity_k3_xboole_0, axiom,
% 2.75/2.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.75/2.99  thf('6', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.75/2.99      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.75/2.99  thf('7', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]:
% 2.75/2.99         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 2.75/2.99           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.75/2.99      inference('demod', [status(thm)], ['5', '6'])).
% 2.75/2.99  thf(t3_boole, axiom,
% 2.75/2.99    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.75/2.99  thf('8', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.75/2.99      inference('cnf', [status(esa)], [t3_boole])).
% 2.75/2.99  thf('9', plain,
% 2.75/2.99      (![X11 : $i, X12 : $i]:
% 2.75/2.99         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 2.75/2.99           = (k3_xboole_0 @ X11 @ X12))),
% 2.75/2.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.75/2.99  thf('10', plain,
% 2.75/2.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.75/2.99      inference('sup+', [status(thm)], ['8', '9'])).
% 2.75/2.99  thf('11', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.75/2.99      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.75/2.99  thf('12', plain,
% 2.75/2.99      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.75/2.99      inference('sup+', [status(thm)], ['10', '11'])).
% 2.75/2.99  thf('13', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]:
% 2.75/2.99         ((k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 2.75/2.99           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.75/2.99      inference('demod', [status(thm)], ['7', '12'])).
% 2.75/2.99  thf(t94_xboole_1, axiom,
% 2.75/2.99    (![A:$i,B:$i]:
% 2.75/2.99     ( ( k2_xboole_0 @ A @ B ) =
% 2.75/2.99       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.75/2.99  thf('14', plain,
% 2.75/2.99      (![X21 : $i, X22 : $i]:
% 2.75/2.99         ((k2_xboole_0 @ X21 @ X22)
% 2.75/2.99           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 2.75/2.99              (k3_xboole_0 @ X21 @ X22)))),
% 2.75/2.99      inference('cnf', [status(esa)], [t94_xboole_1])).
% 2.75/2.99  thf(t91_xboole_1, axiom,
% 2.75/2.99    (![A:$i,B:$i,C:$i]:
% 2.75/2.99     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 2.75/2.99       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 2.75/2.99  thf('15', plain,
% 2.75/2.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 2.75/2.99           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 2.75/2.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.75/2.99  thf('16', plain,
% 2.75/2.99      (![X21 : $i, X22 : $i]:
% 2.75/2.99         ((k2_xboole_0 @ X21 @ X22)
% 2.75/2.99           = (k5_xboole_0 @ X21 @ 
% 2.75/2.99              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 2.75/2.99      inference('demod', [status(thm)], ['14', '15'])).
% 2.75/2.99  thf('17', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]:
% 2.75/2.99         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 2.75/2.99           = (k5_xboole_0 @ X0 @ 
% 2.75/2.99              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 2.75/2.99               (k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))))),
% 2.75/2.99      inference('sup+', [status(thm)], ['13', '16'])).
% 2.75/2.99  thf(t39_xboole_1, axiom,
% 2.75/2.99    (![A:$i,B:$i]:
% 2.75/2.99     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.75/2.99  thf('18', plain,
% 2.75/2.99      (![X8 : $i, X9 : $i]:
% 2.75/2.99         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 2.75/2.99           = (k2_xboole_0 @ X8 @ X9))),
% 2.75/2.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.75/2.99  thf('19', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]:
% 2.75/2.99         ((k2_xboole_0 @ X0 @ X1)
% 2.75/2.99           = (k5_xboole_0 @ X0 @ 
% 2.75/2.99              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 2.75/2.99               (k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))))),
% 2.75/2.99      inference('demod', [status(thm)], ['17', '18'])).
% 2.75/2.99  thf('20', plain,
% 2.75/2.99      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.75/2.99      inference('sup+', [status(thm)], ['10', '11'])).
% 2.75/2.99  thf('21', plain,
% 2.75/2.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.75/2.99      inference('sup+', [status(thm)], ['8', '9'])).
% 2.75/2.99  thf(l98_xboole_1, axiom,
% 2.75/2.99    (![A:$i,B:$i]:
% 2.75/2.99     ( ( k5_xboole_0 @ A @ B ) =
% 2.75/2.99       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.75/2.99  thf('22', plain,
% 2.75/2.99      (![X5 : $i, X6 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ X5 @ X6)
% 2.75/2.99           = (k4_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ (k3_xboole_0 @ X5 @ X6)))),
% 2.75/2.99      inference('cnf', [status(esa)], [l98_xboole_1])).
% 2.75/2.99  thf('23', plain,
% 2.75/2.99      (![X0 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 2.75/2.99           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ 
% 2.75/2.99              (k4_xboole_0 @ X0 @ X0)))),
% 2.75/2.99      inference('sup+', [status(thm)], ['21', '22'])).
% 2.75/2.99  thf(t1_boole, axiom,
% 2.75/2.99    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.75/2.99  thf('24', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 2.75/2.99      inference('cnf', [status(esa)], [t1_boole])).
% 2.75/2.99  thf('25', plain,
% 2.75/2.99      (![X11 : $i, X12 : $i]:
% 2.75/2.99         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 2.75/2.99           = (k3_xboole_0 @ X11 @ X12))),
% 2.75/2.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.75/2.99  thf('26', plain,
% 2.75/2.99      (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 2.75/2.99      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.75/2.99  thf('27', plain,
% 2.75/2.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 2.75/2.99           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 2.75/2.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.75/2.99  thf('28', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X1)
% 2.75/2.99           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1)))),
% 2.75/2.99      inference('sup+', [status(thm)], ['26', '27'])).
% 2.75/2.99  thf('29', plain,
% 2.75/2.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.75/2.99      inference('sup+', [status(thm)], ['8', '9'])).
% 2.75/2.99  thf('30', plain,
% 2.75/2.99      (![X21 : $i, X22 : $i]:
% 2.75/2.99         ((k2_xboole_0 @ X21 @ X22)
% 2.75/2.99           = (k5_xboole_0 @ X21 @ 
% 2.75/2.99              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 2.75/2.99      inference('demod', [status(thm)], ['14', '15'])).
% 2.75/2.99  thf('31', plain,
% 2.75/2.99      (![X0 : $i]:
% 2.75/2.99         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 2.75/2.99           = (k5_xboole_0 @ X0 @ 
% 2.75/2.99              (k5_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))))),
% 2.75/2.99      inference('sup+', [status(thm)], ['29', '30'])).
% 2.75/2.99  thf('32', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 2.75/2.99      inference('cnf', [status(esa)], [t1_boole])).
% 2.75/2.99  thf('33', plain,
% 2.75/2.99      (![X0 : $i]:
% 2.75/2.99         ((X0)
% 2.75/2.99           = (k5_xboole_0 @ X0 @ 
% 2.75/2.99              (k5_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))))),
% 2.75/2.99      inference('demod', [status(thm)], ['31', '32'])).
% 2.75/2.99  thf('34', plain,
% 2.75/2.99      (![X0 : $i]:
% 2.75/2.99         ((X0)
% 2.75/2.99           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0)))),
% 2.75/2.99      inference('sup+', [status(thm)], ['28', '33'])).
% 2.75/2.99  thf('35', plain,
% 2.75/2.99      (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 2.75/2.99      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.75/2.99  thf('36', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X1)
% 2.75/2.99           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1)))),
% 2.75/2.99      inference('sup+', [status(thm)], ['26', '27'])).
% 2.75/2.99  thf('37', plain,
% 2.75/2.99      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.75/2.99      inference('sup+', [status(thm)], ['10', '11'])).
% 2.75/2.99  thf('38', plain,
% 2.75/2.99      (![X5 : $i, X6 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ X5 @ X6)
% 2.75/2.99           = (k4_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ (k3_xboole_0 @ X5 @ X6)))),
% 2.75/2.99      inference('cnf', [status(esa)], [l98_xboole_1])).
% 2.75/2.99  thf('39', plain,
% 2.75/2.99      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 2.75/2.99      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.75/2.99  thf('40', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]:
% 2.75/2.99         (r1_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))),
% 2.75/2.99      inference('sup+', [status(thm)], ['38', '39'])).
% 2.75/2.99  thf('41', plain,
% 2.75/2.99      (![X0 : $i]:
% 2.75/2.99         (r1_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ 
% 2.75/2.99          (k4_xboole_0 @ X0 @ X0))),
% 2.75/2.99      inference('sup+', [status(thm)], ['37', '40'])).
% 2.75/2.99  thf('42', plain,
% 2.75/2.99      (![X15 : $i, X16 : $i]:
% 2.75/2.99         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 2.75/2.99      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.75/2.99  thf('43', plain,
% 2.75/2.99      (![X0 : $i]:
% 2.75/2.99         ((k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ 
% 2.75/2.99           (k4_xboole_0 @ X0 @ X0)) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 2.75/2.99      inference('sup-', [status(thm)], ['41', '42'])).
% 2.75/2.99  thf('44', plain,
% 2.75/2.99      (![X0 : $i]:
% 2.75/2.99         ((k4_xboole_0 @ 
% 2.75/2.99           (k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0) @ 
% 2.75/2.99           (k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ 
% 2.75/2.99            (k5_xboole_0 @ k1_xboole_0 @ X0)))
% 2.75/2.99           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.75/2.99      inference('sup+', [status(thm)], ['36', '43'])).
% 2.75/2.99  thf('45', plain,
% 2.75/2.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.75/2.99      inference('sup+', [status(thm)], ['8', '9'])).
% 2.75/2.99  thf('46', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.75/2.99      inference('cnf', [status(esa)], [t3_boole])).
% 2.75/2.99  thf('47', plain,
% 2.75/2.99      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.75/2.99      inference('sup+', [status(thm)], ['45', '46'])).
% 2.75/2.99  thf('48', plain,
% 2.75/2.99      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.75/2.99      inference('sup+', [status(thm)], ['10', '11'])).
% 2.75/2.99  thf('49', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.75/2.99      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.75/2.99  thf('50', plain,
% 2.75/2.99      (![X11 : $i, X12 : $i]:
% 2.75/2.99         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 2.75/2.99           = (k3_xboole_0 @ X11 @ X12))),
% 2.75/2.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.75/2.99  thf('51', plain,
% 2.75/2.99      (![X11 : $i, X12 : $i]:
% 2.75/2.99         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 2.75/2.99           = (k3_xboole_0 @ X11 @ X12))),
% 2.75/2.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.75/2.99  thf('52', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]:
% 2.75/2.99         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.75/2.99           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.75/2.99      inference('sup+', [status(thm)], ['50', '51'])).
% 2.75/2.99  thf('53', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]:
% 2.75/2.99         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.75/2.99           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.75/2.99      inference('sup+', [status(thm)], ['49', '52'])).
% 2.75/2.99  thf('54', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.75/2.99      inference('cnf', [status(esa)], [t3_boole])).
% 2.75/2.99  thf('55', plain,
% 2.75/2.99      (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 2.75/2.99      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.75/2.99  thf('56', plain,
% 2.75/2.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 2.75/2.99           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 2.75/2.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.75/2.99  thf('57', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X1)
% 2.75/2.99           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1)))),
% 2.75/2.99      inference('sup+', [status(thm)], ['26', '27'])).
% 2.75/2.99  thf('58', plain,
% 2.75/2.99      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.75/2.99      inference('sup+', [status(thm)], ['45', '46'])).
% 2.75/2.99  thf('59', plain,
% 2.75/2.99      (![X0 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 2.75/2.99           = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 2.75/2.99      inference('demod', [status(thm)],
% 2.75/2.99                ['44', '47', '48', '53', '54', '55', '56', '57', '58'])).
% 2.75/2.99  thf('60', plain,
% 2.75/2.99      (![X21 : $i, X22 : $i]:
% 2.75/2.99         ((k2_xboole_0 @ X21 @ X22)
% 2.75/2.99           = (k5_xboole_0 @ X21 @ 
% 2.75/2.99              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 2.75/2.99      inference('demod', [status(thm)], ['14', '15'])).
% 2.75/2.99  thf('61', plain,
% 2.75/2.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 2.75/2.99           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 2.75/2.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.75/2.99  thf('62', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 2.75/2.99           = (k5_xboole_0 @ X1 @ 
% 2.75/2.99              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X2)))),
% 2.75/2.99      inference('sup+', [status(thm)], ['60', '61'])).
% 2.75/2.99  thf('63', plain,
% 2.75/2.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 2.75/2.99           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 2.75/2.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.75/2.99  thf('64', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 2.75/2.99           = (k5_xboole_0 @ X1 @ 
% 2.75/2.99              (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))))),
% 2.75/2.99      inference('demod', [status(thm)], ['62', '63'])).
% 2.75/2.99  thf('65', plain,
% 2.75/2.99      (![X0 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 2.75/2.99           = (k5_xboole_0 @ X0 @ 
% 2.75/2.99              (k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))))),
% 2.75/2.99      inference('sup+', [status(thm)], ['59', '64'])).
% 2.75/2.99  thf('66', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 2.75/2.99      inference('cnf', [status(esa)], [t1_boole])).
% 2.75/2.99  thf('67', plain,
% 2.75/2.99      (![X21 : $i, X22 : $i]:
% 2.75/2.99         ((k2_xboole_0 @ X21 @ X22)
% 2.75/2.99           = (k5_xboole_0 @ X21 @ 
% 2.75/2.99              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 2.75/2.99      inference('demod', [status(thm)], ['14', '15'])).
% 2.75/2.99  thf('68', plain,
% 2.75/2.99      (![X0 : $i]:
% 2.75/2.99         ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 2.75/2.99      inference('demod', [status(thm)], ['65', '66', '67'])).
% 2.75/2.99  thf('69', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 2.75/2.99      inference('cnf', [status(esa)], [t1_boole])).
% 2.75/2.99  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.75/2.99      inference('demod', [status(thm)], ['68', '69'])).
% 2.75/2.99  thf('71', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 2.75/2.99      inference('demod', [status(thm)], ['35', '70'])).
% 2.75/2.99  thf('72', plain,
% 2.75/2.99      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 2.75/2.99      inference('demod', [status(thm)], ['34', '71'])).
% 2.75/2.99  thf('73', plain,
% 2.75/2.99      (![X0 : $i]:
% 2.75/2.99         ((X0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.75/2.99      inference('sup+', [status(thm)], ['20', '72'])).
% 2.75/2.99  thf('74', plain,
% 2.75/2.99      (![X0 : $i, X1 : $i]:
% 2.75/2.99         ((k2_xboole_0 @ X0 @ X1)
% 2.75/2.99           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.75/2.99      inference('demod', [status(thm)], ['19', '73'])).
% 2.75/2.99  thf('75', plain,
% 2.75/2.99      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 2.75/2.99      inference('demod', [status(thm)], ['0', '74'])).
% 2.75/2.99  thf('76', plain, ($false), inference('simplify', [status(thm)], ['75'])).
% 2.75/2.99  
% 2.75/2.99  % SZS output end Refutation
% 2.75/2.99  
% 2.83/3.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
