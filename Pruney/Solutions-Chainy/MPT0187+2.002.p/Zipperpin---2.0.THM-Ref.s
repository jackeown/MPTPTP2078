%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8r9wxGC8wU

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:06 EST 2020

% Result     : Theorem 12.18s
% Output     : Refutation 12.18s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 640 expanded)
%              Number of leaves         :   20 ( 222 expanded)
%              Depth                    :   14
%              Number of atoms          :  773 (7493 expanded)
%              Number of equality atoms :   63 ( 628 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t105_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ C @ D @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t105_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_C @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X10 @ X11 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('7',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_enumset1 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k2_enumset1 @ X1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_enumset1 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('11',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_enumset1 @ X1 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['9','16'])).

thf(t52_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k2_tarski @ X18 @ X19 ) @ ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X10 @ X11 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X1 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X4 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_enumset1 @ X1 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('30',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_enumset1 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 ) @ ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X3 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','36','37'])).

thf('39',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['0','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X3 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','36','37'])).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X10 @ X11 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X1 @ X0 @ X2 @ X3 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X3 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X3 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','36','37'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X3 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','36','37'])).

thf('52',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['39','50','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.09  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8r9wxGC8wU
% 0.08/0.28  % Computer   : n010.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % DateTime   : Tue Dec  1 16:41:59 EST 2020
% 0.08/0.29  % CPUTime    : 
% 0.08/0.29  % Running portfolio for 600 s
% 0.08/0.29  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.08/0.29  % Number of cores: 8
% 0.08/0.29  % Python version: Python 3.6.8
% 0.08/0.29  % Running in FO mode
% 12.18/12.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 12.18/12.38  % Solved by: fo/fo7.sh
% 12.18/12.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.18/12.38  % done 7466 iterations in 11.987s
% 12.18/12.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 12.18/12.38  % SZS output start Refutation
% 12.18/12.38  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 12.18/12.38  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 12.18/12.38  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 12.18/12.38  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 12.18/12.38  thf(sk_D_type, type, sk_D: $i).
% 12.18/12.38  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 12.18/12.38  thf(sk_B_type, type, sk_B: $i).
% 12.18/12.38  thf(sk_C_type, type, sk_C: $i).
% 12.18/12.38  thf(sk_A_type, type, sk_A: $i).
% 12.18/12.38  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 12.18/12.38  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 12.18/12.38  thf(t105_enumset1, conjecture,
% 12.18/12.38    (![A:$i,B:$i,C:$i,D:$i]:
% 12.18/12.38     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 12.18/12.38  thf(zf_stmt_0, negated_conjecture,
% 12.18/12.38    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 12.18/12.38        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ) )),
% 12.18/12.38    inference('cnf.neg', [status(esa)], [t105_enumset1])).
% 12.18/12.38  thf('0', plain,
% 12.18/12.38      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 12.18/12.38         != (k2_enumset1 @ sk_A @ sk_C @ sk_D @ sk_B))),
% 12.18/12.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.18/12.38  thf(t100_enumset1, axiom,
% 12.18/12.38    (![A:$i,B:$i,C:$i]:
% 12.18/12.38     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 12.18/12.38  thf('1', plain,
% 12.18/12.38      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.18/12.38         ((k1_enumset1 @ X12 @ X10 @ X11) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 12.18/12.38      inference('cnf', [status(esa)], [t100_enumset1])).
% 12.18/12.38  thf(t70_enumset1, axiom,
% 12.18/12.38    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 12.18/12.38  thf('2', plain,
% 12.18/12.38      (![X44 : $i, X45 : $i]:
% 12.18/12.38         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 12.18/12.38      inference('cnf', [status(esa)], [t70_enumset1])).
% 12.18/12.38  thf('3', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i]:
% 12.18/12.38         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 12.18/12.38      inference('sup+', [status(thm)], ['1', '2'])).
% 12.18/12.38  thf(t71_enumset1, axiom,
% 12.18/12.38    (![A:$i,B:$i,C:$i]:
% 12.18/12.38     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 12.18/12.38  thf('4', plain,
% 12.18/12.38      (![X46 : $i, X47 : $i, X48 : $i]:
% 12.18/12.38         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 12.18/12.38           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 12.18/12.38      inference('cnf', [status(esa)], [t71_enumset1])).
% 12.18/12.38  thf(t50_enumset1, axiom,
% 12.18/12.38    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 12.18/12.38     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 12.18/12.38       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 12.18/12.38  thf('5', plain,
% 12.18/12.38      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 12.18/12.38         ((k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17)
% 12.18/12.38           = (k2_xboole_0 @ (k2_enumset1 @ X13 @ X14 @ X15 @ X16) @ 
% 12.18/12.38              (k1_tarski @ X17)))),
% 12.18/12.38      inference('cnf', [status(esa)], [t50_enumset1])).
% 12.18/12.38  thf('6', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 12.18/12.38           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 12.18/12.38      inference('sup+', [status(thm)], ['4', '5'])).
% 12.18/12.38  thf(t72_enumset1, axiom,
% 12.18/12.38    (![A:$i,B:$i,C:$i,D:$i]:
% 12.18/12.38     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 12.18/12.38  thf('7', plain,
% 12.18/12.38      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 12.18/12.38         ((k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52)
% 12.18/12.38           = (k2_enumset1 @ X49 @ X50 @ X51 @ X52))),
% 12.18/12.38      inference('cnf', [status(esa)], [t72_enumset1])).
% 12.18/12.38  thf('8', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 12.18/12.38           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 12.18/12.38      inference('sup+', [status(thm)], ['6', '7'])).
% 12.18/12.38  thf('9', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.18/12.38         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 12.18/12.38           = (k2_enumset1 @ X1 @ X0 @ X1 @ X2))),
% 12.18/12.38      inference('sup+', [status(thm)], ['3', '8'])).
% 12.18/12.38  thf('10', plain,
% 12.18/12.38      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 12.18/12.38         ((k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52)
% 12.18/12.38           = (k2_enumset1 @ X49 @ X50 @ X51 @ X52))),
% 12.18/12.38      inference('cnf', [status(esa)], [t72_enumset1])).
% 12.18/12.38  thf('11', plain,
% 12.18/12.38      (![X46 : $i, X47 : $i, X48 : $i]:
% 12.18/12.38         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 12.18/12.38           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 12.18/12.38      inference('cnf', [status(esa)], [t71_enumset1])).
% 12.18/12.38  thf('12', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.18/12.38         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 12.18/12.38      inference('sup+', [status(thm)], ['10', '11'])).
% 12.18/12.38  thf('13', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 12.18/12.38           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 12.18/12.38      inference('sup+', [status(thm)], ['4', '5'])).
% 12.18/12.38  thf('14', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.18/12.38         ((k1_enumset1 @ X2 @ X1 @ X0)
% 12.18/12.38           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 12.18/12.38      inference('sup+', [status(thm)], ['12', '13'])).
% 12.18/12.38  thf('15', plain,
% 12.18/12.38      (![X44 : $i, X45 : $i]:
% 12.18/12.38         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 12.18/12.38      inference('cnf', [status(esa)], [t70_enumset1])).
% 12.18/12.38  thf('16', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.18/12.38         ((k1_enumset1 @ X2 @ X1 @ X0)
% 12.18/12.38           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 12.18/12.38      inference('demod', [status(thm)], ['14', '15'])).
% 12.18/12.38  thf('17', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.18/12.38         ((k1_enumset1 @ X1 @ X0 @ X2) = (k2_enumset1 @ X1 @ X0 @ X1 @ X2))),
% 12.18/12.38      inference('demod', [status(thm)], ['9', '16'])).
% 12.18/12.38  thf(t52_enumset1, axiom,
% 12.18/12.38    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 12.18/12.38     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 12.18/12.38       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ))).
% 12.18/12.38  thf('18', plain,
% 12.18/12.38      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 12.18/12.38         ((k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 12.18/12.38           = (k2_xboole_0 @ (k2_tarski @ X18 @ X19) @ 
% 12.18/12.38              (k2_enumset1 @ X20 @ X21 @ X22 @ X23)))),
% 12.18/12.38      inference('cnf', [status(esa)], [t52_enumset1])).
% 12.18/12.38  thf('19', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.18/12.38         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X2 @ X0)
% 12.18/12.38           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 12.18/12.38              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 12.18/12.38      inference('sup+', [status(thm)], ['17', '18'])).
% 12.18/12.38  thf('20', plain,
% 12.18/12.38      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.18/12.38         ((k1_enumset1 @ X12 @ X10 @ X11) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 12.18/12.38      inference('cnf', [status(esa)], [t100_enumset1])).
% 12.18/12.38  thf('21', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i]:
% 12.18/12.38         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 12.18/12.38      inference('sup+', [status(thm)], ['1', '2'])).
% 12.18/12.38  thf(l62_enumset1, axiom,
% 12.18/12.38    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 12.18/12.38     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 12.18/12.38       ( k2_xboole_0 @
% 12.18/12.38         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 12.18/12.38  thf('22', plain,
% 12.18/12.38      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 12.18/12.38         ((k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 12.18/12.38           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 12.18/12.38              (k1_enumset1 @ X7 @ X8 @ X9)))),
% 12.18/12.38      inference('cnf', [status(esa)], [l62_enumset1])).
% 12.18/12.38  thf('23', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.18/12.38         ((k4_enumset1 @ X1 @ X0 @ X1 @ X4 @ X3 @ X2)
% 12.18/12.38           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 12.18/12.38              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 12.18/12.38      inference('sup+', [status(thm)], ['21', '22'])).
% 12.18/12.38  thf('24', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.18/12.38         ((k4_enumset1 @ X4 @ X3 @ X4 @ X0 @ X2 @ X1)
% 12.18/12.38           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 12.18/12.38              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 12.18/12.38      inference('sup+', [status(thm)], ['20', '23'])).
% 12.18/12.38  thf('25', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 12.18/12.38           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ 
% 12.18/12.38              (k1_enumset1 @ X2 @ X0 @ X1)))),
% 12.18/12.38      inference('sup+', [status(thm)], ['19', '24'])).
% 12.18/12.38  thf('26', plain,
% 12.18/12.38      (![X44 : $i, X45 : $i]:
% 12.18/12.38         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 12.18/12.38      inference('cnf', [status(esa)], [t70_enumset1])).
% 12.18/12.38  thf('27', plain,
% 12.18/12.38      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 12.18/12.38         ((k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 12.18/12.38           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 12.18/12.38              (k1_enumset1 @ X7 @ X8 @ X9)))),
% 12.18/12.38      inference('cnf', [status(esa)], [l62_enumset1])).
% 12.18/12.38  thf('28', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.18/12.38         ((k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 12.18/12.38           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 12.18/12.38              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 12.18/12.38      inference('sup+', [status(thm)], ['26', '27'])).
% 12.18/12.38  thf('29', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.18/12.38         ((k1_enumset1 @ X1 @ X0 @ X2) = (k2_enumset1 @ X1 @ X0 @ X1 @ X2))),
% 12.18/12.38      inference('demod', [status(thm)], ['9', '16'])).
% 12.18/12.38  thf('30', plain,
% 12.18/12.38      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 12.18/12.38         ((k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52)
% 12.18/12.38           = (k2_enumset1 @ X49 @ X50 @ X51 @ X52))),
% 12.18/12.38      inference('cnf', [status(esa)], [t72_enumset1])).
% 12.18/12.38  thf('31', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.18/12.38         ((k3_enumset1 @ X2 @ X2 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 12.18/12.38      inference('sup+', [status(thm)], ['29', '30'])).
% 12.18/12.38  thf(t55_enumset1, axiom,
% 12.18/12.38    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 12.18/12.38     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 12.18/12.38       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 12.18/12.38  thf('32', plain,
% 12.18/12.38      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 12.18/12.38         ((k4_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29)
% 12.18/12.38           = (k2_xboole_0 @ (k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28) @ 
% 12.18/12.38              (k1_tarski @ X29)))),
% 12.18/12.38      inference('cnf', [status(esa)], [t55_enumset1])).
% 12.18/12.38  thf('33', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k4_enumset1 @ X2 @ X2 @ X1 @ X2 @ X0 @ X3)
% 12.18/12.38           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 12.18/12.38      inference('sup+', [status(thm)], ['31', '32'])).
% 12.18/12.38  thf('34', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 12.18/12.38           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 12.18/12.38      inference('sup+', [status(thm)], ['6', '7'])).
% 12.18/12.38  thf('35', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k4_enumset1 @ X2 @ X2 @ X1 @ X2 @ X0 @ X3)
% 12.18/12.38           = (k2_enumset1 @ X2 @ X1 @ X0 @ X3))),
% 12.18/12.38      inference('demod', [status(thm)], ['33', '34'])).
% 12.18/12.38  thf('36', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 12.18/12.38           = (k2_enumset1 @ X2 @ X3 @ X1 @ X0))),
% 12.18/12.38      inference('sup+', [status(thm)], ['28', '35'])).
% 12.18/12.38  thf('37', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 12.18/12.38           = (k2_enumset1 @ X2 @ X3 @ X1 @ X0))),
% 12.18/12.38      inference('sup+', [status(thm)], ['28', '35'])).
% 12.18/12.38  thf('38', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0) = (k2_enumset1 @ X2 @ X3 @ X0 @ X1))),
% 12.18/12.38      inference('demod', [status(thm)], ['25', '36', '37'])).
% 12.18/12.38  thf('39', plain,
% 12.18/12.38      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 12.18/12.38         != (k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D))),
% 12.18/12.38      inference('demod', [status(thm)], ['0', '38'])).
% 12.18/12.38  thf('40', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0) = (k2_enumset1 @ X2 @ X3 @ X0 @ X1))),
% 12.18/12.38      inference('demod', [status(thm)], ['25', '36', '37'])).
% 12.18/12.38  thf('41', plain,
% 12.18/12.38      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.18/12.38         ((k1_enumset1 @ X12 @ X10 @ X11) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 12.18/12.38      inference('cnf', [status(esa)], [t100_enumset1])).
% 12.18/12.38  thf('42', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 12.18/12.38           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 12.18/12.38      inference('sup+', [status(thm)], ['6', '7'])).
% 12.18/12.38  thf('43', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 12.18/12.38           = (k2_enumset1 @ X1 @ X0 @ X2 @ X3))),
% 12.18/12.38      inference('sup+', [status(thm)], ['41', '42'])).
% 12.18/12.38  thf('44', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 12.18/12.38           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 12.18/12.38      inference('sup+', [status(thm)], ['6', '7'])).
% 12.18/12.38  thf('45', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X3 @ X2 @ X0))),
% 12.18/12.38      inference('sup+', [status(thm)], ['43', '44'])).
% 12.18/12.38  thf('46', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_enumset1 @ X2 @ X0 @ X3 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 12.18/12.38      inference('sup+', [status(thm)], ['40', '45'])).
% 12.18/12.38  thf('47', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0) = (k2_enumset1 @ X2 @ X3 @ X0 @ X1))),
% 12.18/12.38      inference('demod', [status(thm)], ['25', '36', '37'])).
% 12.18/12.38  thf('48', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X3 @ X2 @ X0))),
% 12.18/12.38      inference('sup+', [status(thm)], ['43', '44'])).
% 12.18/12.38  thf('49', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 12.18/12.38      inference('sup+', [status(thm)], ['47', '48'])).
% 12.18/12.38  thf('50', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_enumset1 @ X3 @ X0 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 12.18/12.38      inference('sup+', [status(thm)], ['46', '49'])).
% 12.18/12.38  thf('51', plain,
% 12.18/12.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.18/12.38         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0) = (k2_enumset1 @ X2 @ X3 @ X0 @ X1))),
% 12.18/12.38      inference('demod', [status(thm)], ['25', '36', '37'])).
% 12.18/12.38  thf('52', plain,
% 12.18/12.38      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 12.18/12.38         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 12.18/12.38      inference('demod', [status(thm)], ['39', '50', '51'])).
% 12.18/12.38  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 12.18/12.38  
% 12.18/12.38  % SZS output end Refutation
% 12.18/12.38  
% 12.18/12.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
