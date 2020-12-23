%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9j7uaM3Ib1

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:33 EST 2020

% Result     : Theorem 6.43s
% Output     : Refutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :   66 (  82 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :  664 ( 840 expanded)
%              Number of equality atoms :   54 (  70 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t137_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t137_enumset1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('6',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k6_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 ) @ ( k2_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X6 @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('9',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k6_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 )
      = ( k5_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) )
      = ( k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X3 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('12',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k5_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k4_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('13',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) )
      = ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf(t113_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X13 @ X10 @ X12 @ X11 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X8 @ X7 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X3 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X3 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X13 @ X10 @ X12 @ X11 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X8 @ X7 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X17 @ X16 @ X15 @ X14 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X17 @ X16 @ X15 @ X14 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X8 @ X7 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X17 @ X16 @ X15 @ X14 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('30',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X8 @ X7 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X17 @ X16 @ X15 @ X14 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X8 @ X7 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('36',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','15','20','25','28','33','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9j7uaM3Ib1
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.43/6.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.43/6.61  % Solved by: fo/fo7.sh
% 6.43/6.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.43/6.61  % done 8373 iterations in 6.157s
% 6.43/6.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.43/6.61  % SZS output start Refutation
% 6.43/6.61  thf(sk_A_type, type, sk_A: $i).
% 6.43/6.61  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 6.43/6.61  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 6.43/6.61  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 6.43/6.61  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 6.43/6.61                                           $i > $i).
% 6.43/6.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 6.43/6.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.43/6.61  thf(sk_B_type, type, sk_B: $i).
% 6.43/6.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.43/6.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 6.43/6.61  thf(sk_C_type, type, sk_C: $i).
% 6.43/6.61  thf(t137_enumset1, conjecture,
% 6.43/6.61    (![A:$i,B:$i,C:$i]:
% 6.43/6.61     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 6.43/6.61       ( k1_enumset1 @ A @ B @ C ) ))).
% 6.43/6.61  thf(zf_stmt_0, negated_conjecture,
% 6.43/6.61    (~( ![A:$i,B:$i,C:$i]:
% 6.43/6.61        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 6.43/6.61          ( k1_enumset1 @ A @ B @ C ) ) )),
% 6.43/6.61    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 6.43/6.61  thf('0', plain,
% 6.43/6.61      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 6.43/6.61         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 6.43/6.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.43/6.61  thf(t72_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i,D:$i]:
% 6.43/6.61     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 6.43/6.61  thf('1', plain,
% 6.43/6.61      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43)
% 6.43/6.61           = (k2_enumset1 @ X40 @ X41 @ X42 @ X43))),
% 6.43/6.61      inference('cnf', [status(esa)], [t72_enumset1])).
% 6.43/6.61  thf(t71_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i]:
% 6.43/6.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 6.43/6.61  thf('2', plain,
% 6.43/6.61      (![X37 : $i, X38 : $i, X39 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 6.43/6.61           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 6.43/6.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.43/6.61  thf('3', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['1', '2'])).
% 6.43/6.61  thf(t70_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 6.43/6.61  thf('4', plain,
% 6.43/6.61      (![X35 : $i, X36 : $i]:
% 6.43/6.61         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 6.43/6.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 6.43/6.61  thf('5', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['3', '4'])).
% 6.43/6.61  thf(t73_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.43/6.61     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 6.43/6.61       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 6.43/6.61  thf('6', plain,
% 6.43/6.61      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 6.43/6.61         ((k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48)
% 6.43/6.61           = (k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 6.43/6.61      inference('cnf', [status(esa)], [t73_enumset1])).
% 6.43/6.61  thf(t67_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 6.43/6.61     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 6.43/6.61       ( k2_xboole_0 @
% 6.43/6.61         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 6.43/6.61  thf('7', plain,
% 6.43/6.61      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, 
% 6.43/6.61         X34 : $i]:
% 6.43/6.61         ((k6_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34)
% 6.43/6.61           = (k2_xboole_0 @ 
% 6.43/6.61              (k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32) @ 
% 6.43/6.61              (k2_tarski @ X33 @ X34)))),
% 6.43/6.61      inference('cnf', [status(esa)], [t67_enumset1])).
% 6.43/6.61  thf('8', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 6.43/6.61         ((k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5)
% 6.43/6.61           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 6.43/6.61              (k2_tarski @ X6 @ X5)))),
% 6.43/6.61      inference('sup+', [status(thm)], ['6', '7'])).
% 6.43/6.61  thf(t75_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 6.43/6.61     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 6.43/6.61       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 6.43/6.61  thf('9', plain,
% 6.43/6.61      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 6.43/6.61         ((k6_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61)
% 6.43/6.61           = (k5_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61))),
% 6.43/6.61      inference('cnf', [status(esa)], [t75_enumset1])).
% 6.43/6.61  thf('10', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 6.43/6.61         ((k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 6.43/6.61           (k2_tarski @ X1 @ X0))
% 6.43/6.61           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['8', '9'])).
% 6.43/6.61  thf('11', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2))
% 6.43/6.61           = (k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X3 @ X2))),
% 6.43/6.61      inference('sup+', [status(thm)], ['5', '10'])).
% 6.43/6.61  thf(t74_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.43/6.61     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 6.43/6.61       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 6.43/6.61  thf('12', plain,
% 6.43/6.61      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 6.43/6.61         ((k5_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54)
% 6.43/6.61           = (k4_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 6.43/6.61      inference('cnf', [status(esa)], [t74_enumset1])).
% 6.43/6.61  thf('13', plain,
% 6.43/6.61      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 6.43/6.61         ((k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48)
% 6.43/6.61           = (k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 6.43/6.61      inference('cnf', [status(esa)], [t73_enumset1])).
% 6.43/6.61  thf('14', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.43/6.61         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 6.43/6.61           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['12', '13'])).
% 6.43/6.61  thf('15', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2))
% 6.43/6.61           = (k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2))),
% 6.43/6.61      inference('demod', [status(thm)], ['11', '14'])).
% 6.43/6.61  thf(t113_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i,D:$i]:
% 6.43/6.61     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 6.43/6.61  thf('16', plain,
% 6.43/6.61      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X13 @ X10 @ X12 @ X11)
% 6.43/6.61           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 6.43/6.61      inference('cnf', [status(esa)], [t113_enumset1])).
% 6.43/6.61  thf(t107_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i,D:$i]:
% 6.43/6.61     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 6.43/6.61  thf('17', plain,
% 6.43/6.61      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X6 @ X9 @ X8 @ X7) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 6.43/6.61      inference('cnf', [status(esa)], [t107_enumset1])).
% 6.43/6.61  thf('18', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X0 @ X2 @ X1 @ X3) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['16', '17'])).
% 6.43/6.61  thf('19', plain,
% 6.43/6.61      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43)
% 6.43/6.61           = (k2_enumset1 @ X40 @ X41 @ X42 @ X43))),
% 6.43/6.61      inference('cnf', [status(esa)], [t72_enumset1])).
% 6.43/6.61  thf('20', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X3)
% 6.43/6.61           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['18', '19'])).
% 6.43/6.61  thf('21', plain,
% 6.43/6.61      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X13 @ X10 @ X12 @ X11)
% 6.43/6.61           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 6.43/6.61      inference('cnf', [status(esa)], [t113_enumset1])).
% 6.43/6.61  thf('22', plain,
% 6.43/6.61      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X6 @ X9 @ X8 @ X7) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 6.43/6.61      inference('cnf', [status(esa)], [t107_enumset1])).
% 6.43/6.61  thf('23', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['21', '22'])).
% 6.43/6.61  thf(t125_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i,D:$i]:
% 6.43/6.61     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 6.43/6.61  thf('24', plain,
% 6.43/6.61      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X17 @ X16 @ X15 @ X14)
% 6.43/6.61           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 6.43/6.61      inference('cnf', [status(esa)], [t125_enumset1])).
% 6.43/6.61  thf('25', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['23', '24'])).
% 6.43/6.61  thf('26', plain,
% 6.43/6.61      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X17 @ X16 @ X15 @ X14)
% 6.43/6.61           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 6.43/6.61      inference('cnf', [status(esa)], [t125_enumset1])).
% 6.43/6.61  thf('27', plain,
% 6.43/6.61      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X6 @ X9 @ X8 @ X7) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 6.43/6.61      inference('cnf', [status(esa)], [t107_enumset1])).
% 6.43/6.61  thf('28', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['26', '27'])).
% 6.43/6.61  thf('29', plain,
% 6.43/6.61      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X17 @ X16 @ X15 @ X14)
% 6.43/6.61           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 6.43/6.61      inference('cnf', [status(esa)], [t125_enumset1])).
% 6.43/6.61  thf('30', plain,
% 6.43/6.61      (![X37 : $i, X38 : $i, X39 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 6.43/6.61           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 6.43/6.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.43/6.61  thf('31', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 6.43/6.61      inference('sup+', [status(thm)], ['29', '30'])).
% 6.43/6.61  thf('32', plain,
% 6.43/6.61      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X6 @ X9 @ X8 @ X7) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 6.43/6.61      inference('cnf', [status(esa)], [t107_enumset1])).
% 6.43/6.61  thf('33', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X0 @ X2 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['31', '32'])).
% 6.43/6.61  thf('34', plain,
% 6.43/6.61      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X17 @ X16 @ X15 @ X14)
% 6.43/6.61           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 6.43/6.61      inference('cnf', [status(esa)], [t125_enumset1])).
% 6.43/6.61  thf('35', plain,
% 6.43/6.61      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X6 @ X9 @ X8 @ X7) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 6.43/6.61      inference('cnf', [status(esa)], [t107_enumset1])).
% 6.43/6.61  thf('36', plain,
% 6.43/6.61      (![X37 : $i, X38 : $i, X39 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 6.43/6.61           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 6.43/6.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.43/6.61  thf('37', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 6.43/6.61      inference('sup+', [status(thm)], ['35', '36'])).
% 6.43/6.61  thf('38', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 6.43/6.61      inference('sup+', [status(thm)], ['34', '37'])).
% 6.43/6.61  thf('39', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 6.43/6.61      inference('sup+', [status(thm)], ['35', '36'])).
% 6.43/6.61  thf('40', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 6.43/6.61      inference('sup+', [status(thm)], ['38', '39'])).
% 6.43/6.61  thf('41', plain,
% 6.43/6.61      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 6.43/6.61         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 6.43/6.61      inference('demod', [status(thm)],
% 6.43/6.61                ['0', '15', '20', '25', '28', '33', '40'])).
% 6.43/6.61  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 6.43/6.61  
% 6.43/6.61  % SZS output end Refutation
% 6.43/6.61  
% 6.43/6.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
