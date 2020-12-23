%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UPLDqqe0b5

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:27 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 107 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :  674 (1055 expanded)
%              Number of equality atoms :   58 (  96 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t71_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_enumset1 @ A @ A @ B @ C )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X57: $i] :
      ( ( k2_tarski @ X57 @ X57 )
      = ( k1_tarski @ X57 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k1_enumset1 @ X58 @ X58 @ X59 )
      = ( k2_tarski @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X57: $i] :
      ( ( k2_tarski @ X57 @ X57 )
      = ( k1_tarski @ X57 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    ! [X57: $i] :
      ( ( k2_tarski @ X57 @ X57 )
      = ( k1_tarski @ X57 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k2_tarski @ X20 @ X21 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k1_enumset1 @ X58 @ X58 @ X59 )
      = ( k2_tarski @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_tarski @ X27 ) @ ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('17',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 ) @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k2_tarski @ X20 @ X21 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k1_enumset1 @ X58 @ X58 @ X59 )
      = ( k2_tarski @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X14 @ X15 @ X16 ) @ ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X9 @ X10 @ X11 ) @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k1_enumset1 @ X58 @ X58 @ X59 )
      = ( k2_tarski @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('28',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k2_tarski @ X32 @ X33 ) @ ( k1_enumset1 @ X34 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k1_enumset1 @ X58 @ X58 @ X59 )
      = ( k2_tarski @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X9 @ X10 @ X11 ) @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X57: $i] :
      ( ( k2_tarski @ X57 @ X57 )
      = ( k1_tarski @ X57 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k2_tarski @ X32 @ X33 ) @ ( k1_enumset1 @ X34 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UPLDqqe0b5
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:31:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 300 iterations in 0.130s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.36/0.58  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.58  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.58  thf(t71_enumset1, conjecture,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.58        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.36/0.58  thf('0', plain,
% 0.36/0.58      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.36/0.58         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(t69_enumset1, axiom,
% 0.36/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.58  thf('1', plain, (![X57 : $i]: ((k2_tarski @ X57 @ X57) = (k1_tarski @ X57))),
% 0.36/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.58  thf(t70_enumset1, axiom,
% 0.36/0.58    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.58  thf('2', plain,
% 0.36/0.58      (![X58 : $i, X59 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X58 @ X58 @ X59) = (k2_tarski @ X58 @ X59))),
% 0.36/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.58  thf(t44_enumset1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.58     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.36/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.36/0.58  thf('3', plain,
% 0.36/0.58      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X23 @ X24 @ X25 @ X26)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k1_enumset1 @ X24 @ X25 @ X26)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.36/0.58  thf('4', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('5', plain, (![X57 : $i]: ((k2_tarski @ X57 @ X57) = (k1_tarski @ X57))),
% 0.36/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.58  thf('6', plain, (![X57 : $i]: ((k2_tarski @ X57 @ X57) = (k1_tarski @ X57))),
% 0.36/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.58  thf(t43_enumset1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.36/0.58       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.36/0.58  thf('7', plain,
% 0.36/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X20 @ X21) @ (k1_tarski @ X22)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.36/0.58  thf('8', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.36/0.58  thf('9', plain,
% 0.36/0.58      (![X58 : $i, X59 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X58 @ X58 @ X59) = (k2_tarski @ X58 @ X59))),
% 0.36/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.58  thf('10', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((k2_tarski @ X0 @ X1)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.36/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.58  thf('11', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((k2_tarski @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['5', '10'])).
% 0.36/0.58  thf('12', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((k2_tarski @ X1 @ X0) = (k2_enumset1 @ X1 @ X0 @ X0 @ X0))),
% 0.36/0.58      inference('sup+', [status(thm)], ['4', '11'])).
% 0.36/0.58  thf('13', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((k2_tarski @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['5', '10'])).
% 0.36/0.58  thf('14', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((k2_tarski @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.36/0.58              (k2_enumset1 @ X0 @ X0 @ X0 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['12', '13'])).
% 0.36/0.58  thf(t47_enumset1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.58     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.36/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.36/0.58  thf('15', plain,
% 0.36/0.58      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.36/0.58         ((k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X27) @ 
% 0.36/0.58              (k2_enumset1 @ X28 @ X29 @ X30 @ X31)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((k2_tarski @ X1 @ X0) = (k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.36/0.58  thf(t55_enumset1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.58     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.36/0.58       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.36/0.58  thf('17', plain,
% 0.36/0.58      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.36/0.58         ((k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.36/0.58           = (k2_xboole_0 @ (k3_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41) @ 
% 0.36/0.58              (k1_tarski @ X42)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.36/0.58  thf('18', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k4_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0 @ X2)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['16', '17'])).
% 0.36/0.58  thf('19', plain,
% 0.36/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X20 @ X21) @ (k1_tarski @ X22)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.36/0.58  thf('20', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k4_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0 @ X2)
% 0.36/0.58           = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.36/0.58      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.58  thf('21', plain,
% 0.36/0.58      (![X58 : $i, X59 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X58 @ X58 @ X59) = (k2_tarski @ X58 @ X59))),
% 0.36/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.58  thf(l62_enumset1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.58     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.36/0.58       ( k2_xboole_0 @
% 0.36/0.58         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.36/0.58  thf('22', plain,
% 0.36/0.58      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.58         ((k4_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.36/0.58           = (k2_xboole_0 @ (k1_enumset1 @ X14 @ X15 @ X16) @ 
% 0.36/0.58              (k1_enumset1 @ X17 @ X18 @ X19)))),
% 0.36/0.58      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.36/0.58  thf('23', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 0.36/0.58              (k2_tarski @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['21', '22'])).
% 0.36/0.58  thf(l57_enumset1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.58     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.36/0.58       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.36/0.58  thf('24', plain,
% 0.36/0.58      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.36/0.58         ((k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.36/0.58           = (k2_xboole_0 @ (k1_enumset1 @ X9 @ X10 @ X11) @ 
% 0.36/0.58              (k2_tarski @ X12 @ X13)))),
% 0.36/0.58      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.36/0.58  thf('25', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.36/0.58           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.58  thf('26', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X2 @ X1 @ X0) = (k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0))),
% 0.36/0.58      inference('sup+', [status(thm)], ['20', '25'])).
% 0.36/0.58  thf('27', plain,
% 0.36/0.58      (![X58 : $i, X59 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X58 @ X58 @ X59) = (k2_tarski @ X58 @ X59))),
% 0.36/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.58  thf(t48_enumset1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.58     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.36/0.58       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.36/0.58  thf('28', plain,
% 0.36/0.58      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.36/0.58         ((k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X32 @ X33) @ 
% 0.36/0.58              (k1_enumset1 @ X34 @ X35 @ X36)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.36/0.58  thf('29', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['27', '28'])).
% 0.36/0.58  thf('30', plain,
% 0.36/0.58      (![X58 : $i, X59 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X58 @ X58 @ X59) = (k2_tarski @ X58 @ X59))),
% 0.36/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.58  thf('31', plain,
% 0.36/0.58      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.36/0.58         ((k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.36/0.58           = (k2_xboole_0 @ (k1_enumset1 @ X9 @ X10 @ X11) @ 
% 0.36/0.58              (k2_tarski @ X12 @ X13)))),
% 0.36/0.58      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.36/0.58  thf('32', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['30', '31'])).
% 0.36/0.58  thf('33', plain,
% 0.36/0.58      (![X57 : $i]: ((k2_tarski @ X57 @ X57) = (k1_tarski @ X57))),
% 0.36/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.58  thf('34', plain,
% 0.36/0.58      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.36/0.58         ((k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X32 @ X33) @ 
% 0.36/0.58              (k1_enumset1 @ X34 @ X35 @ X36)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.36/0.58  thf('35', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['33', '34'])).
% 0.36/0.58  thf('36', plain,
% 0.36/0.58      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X23 @ X24 @ X25 @ X26)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k1_enumset1 @ X24 @ X25 @ X26)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.36/0.58  thf('37', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.36/0.58           = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 0.36/0.58      inference('demod', [status(thm)], ['35', '36'])).
% 0.36/0.58  thf('38', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.36/0.58      inference('demod', [status(thm)], ['32', '37'])).
% 0.36/0.58  thf('39', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.36/0.58           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['29', '38'])).
% 0.36/0.58  thf('40', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['26', '39'])).
% 0.36/0.58  thf('41', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('42', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.58  thf('43', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X0 @ X2 @ X1)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['1', '42'])).
% 0.36/0.58  thf('44', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.36/0.58      inference('demod', [status(thm)], ['32', '37'])).
% 0.36/0.58  thf('45', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X0 @ X2 @ X1) = (k2_enumset1 @ X0 @ X0 @ X2 @ X1))),
% 0.36/0.58      inference('demod', [status(thm)], ['43', '44'])).
% 0.36/0.58  thf('46', plain,
% 0.36/0.58      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.36/0.58         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.36/0.58      inference('demod', [status(thm)], ['0', '45'])).
% 0.36/0.58  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
