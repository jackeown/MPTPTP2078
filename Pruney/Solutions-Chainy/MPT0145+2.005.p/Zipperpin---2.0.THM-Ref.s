%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wYdSJ6Fyxn

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 130 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  741 (1621 expanded)
%              Number of equality atoms :   48 ( 114 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t61_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
        = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k2_xboole_0 @ ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tarski @ sk_G ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 ) @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X32 @ X33 @ X34 ) @ ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_tarski @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 ) @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t58_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ) )).

thf('33',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( k5_enumset1 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X53 @ X54 @ X55 ) @ ( k2_enumset1 @ X56 @ X57 @ X58 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','34'])).

thf('36',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['0','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wYdSJ6Fyxn
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:40:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 57 iterations in 0.052s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.51  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.51  thf(t61_enumset1, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.22/0.51     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.22/0.51       ( k2_xboole_0 @
% 0.22/0.51         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.22/0.51        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.22/0.51          ( k2_xboole_0 @
% 0.22/0.51            ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t61_enumset1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.22/0.51         != (k2_xboole_0 @ 
% 0.22/0.51             (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.22/0.51             (k1_tarski @ sk_G)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t55_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.51     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.51       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.22/0.51         ((k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52)
% 0.22/0.51           = (k2_xboole_0 @ (k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51) @ 
% 0.22/0.51              (k1_tarski @ X52)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.22/0.51  thf(t46_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.22/0.51       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.22/0.51         ((k2_enumset1 @ X32 @ X33 @ X34 @ X35)
% 0.22/0.51           = (k2_xboole_0 @ (k1_enumset1 @ X32 @ X33 @ X34) @ (k1_tarski @ X35)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.22/0.51  thf(t44_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.22/0.51       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.51         ((k2_enumset1 @ X24 @ X25 @ X26 @ X27)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X24) @ (k1_enumset1 @ X25 @ X26 @ X27)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.22/0.51  thf(t4_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.51       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.22/0.51           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.22/0.51              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.22/0.51              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['2', '5'])).
% 0.22/0.51  thf(t45_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.22/0.51       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.22/0.51         ((k2_enumset1 @ X28 @ X29 @ X30 @ X31)
% 0.22/0.51           = (k2_xboole_0 @ (k2_tarski @ X28 @ X29) @ (k2_tarski @ X30 @ X31)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.22/0.51  thf(t42_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.22/0.51       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.51         ((k1_enumset1 @ X21 @ X22 @ X23)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X21) @ (k2_tarski @ X22 @ X23)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.22/0.51           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.22/0.51              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.22/0.51              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['7', '10'])).
% 0.22/0.51  thf(l57_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.51     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.22/0.51       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.51         ((k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.22/0.51           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X8 @ X9) @ 
% 0.22/0.51              (k2_tarski @ X10 @ X11)))),
% 0.22/0.51      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.22/0.51              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.22/0.51           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['6', '13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.22/0.51              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.22/0.51           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.22/0.51              (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X5)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.22/0.51           (k1_tarski @ X0))
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.22/0.51              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['14', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.22/0.51         ((k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52)
% 0.22/0.51           = (k2_xboole_0 @ (k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51) @ 
% 0.22/0.51              (k1_tarski @ X52)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.22/0.51              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.22/0.51           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.22/0.51              (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.22/0.51           (k1_tarski @ X0))
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.22/0.51              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['1', '22'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.22/0.51              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.51  thf(t41_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k2_tarski @ A @ B ) =
% 0.22/0.51       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (![X19 : $i, X20 : $i]:
% 0.22/0.51         ((k2_tarski @ X19 @ X20)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X20)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.22/0.51           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.22/0.51              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['25', '26'])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.22/0.51           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.22/0.51              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['24', '27'])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.22/0.51              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.22/0.51           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.22/0.51              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['28', '29'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.22/0.51              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 0.22/0.51           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.22/0.51              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['30', '31'])).
% 0.22/0.51  thf(t58_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.22/0.51     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.22/0.51       ( k2_xboole_0 @
% 0.22/0.51         ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ))).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.22/0.51         ((k5_enumset1 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59)
% 0.22/0.51           = (k2_xboole_0 @ (k1_enumset1 @ X53 @ X54 @ X55) @ 
% 0.22/0.51              (k2_enumset1 @ X56 @ X57 @ X58 @ X59)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t58_enumset1])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.22/0.51              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.22/0.51           (k1_tarski @ X0)) = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['23', '34'])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.22/0.51         != (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.22/0.51      inference('demod', [status(thm)], ['0', '35'])).
% 0.22/0.51  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
