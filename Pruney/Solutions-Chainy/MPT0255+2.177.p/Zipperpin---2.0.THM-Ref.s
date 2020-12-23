%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XuXPbWSSg2

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:16 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   75 (  79 expanded)
%              Number of leaves         :   32 (  36 expanded)
%              Depth                    :   17
%              Number of atoms          :  526 ( 549 expanded)
%              Number of equality atoms :   65 (  70 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k2_enumset1 @ X39 @ X39 @ X40 @ X41 )
      = ( k1_enumset1 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k3_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 )
      = ( k2_enumset1 @ X42 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('7',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k4_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 @ X50 )
      = ( k3_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('8',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k5_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 )
      = ( k4_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('9',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k6_enumset1 @ X57 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 )
      = ( k5_enumset1 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k6_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_tarski @ X28 ) @ ( k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k1_tarski @ X7 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('13',plain,(
    ! [X66: $i,X67: $i] :
      ( ( X67 != X66 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X67 ) @ ( k1_tarski @ X66 ) )
       != ( k1_tarski @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('14',plain,(
    ! [X66: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X66 ) @ ( k1_tarski @ X66 ) )
     != ( k1_tarski @ X66 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('21',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','26'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X66: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X66 ) ) ),
    inference(demod,[status(thm)],['14','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['12','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','38'])).

thf('40',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XuXPbWSSg2
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:11:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.54/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.71  % Solved by: fo/fo7.sh
% 0.54/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.71  % done 720 iterations in 0.263s
% 0.54/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.71  % SZS output start Refutation
% 0.54/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.71  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.54/0.71  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.54/0.71  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.54/0.71                                           $i > $i).
% 0.54/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.54/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.54/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.54/0.71  thf(t50_zfmisc_1, conjecture,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.54/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.71        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.54/0.71    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.54/0.71  thf('0', plain,
% 0.54/0.71      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(t15_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.71       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.71  thf('1', plain,
% 0.54/0.71      (![X3 : $i, X4 : $i]:
% 0.54/0.71         (((X3) = (k1_xboole_0)) | ((k2_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.54/0.71  thf('2', plain,
% 0.54/0.71      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.71        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.71  thf('3', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.54/0.71      inference('simplify', [status(thm)], ['2'])).
% 0.54/0.71  thf(t70_enumset1, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.54/0.71  thf('4', plain,
% 0.54/0.71      (![X37 : $i, X38 : $i]:
% 0.54/0.71         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.54/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.54/0.71  thf(t71_enumset1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.54/0.71  thf('5', plain,
% 0.54/0.71      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.54/0.71         ((k2_enumset1 @ X39 @ X39 @ X40 @ X41)
% 0.54/0.71           = (k1_enumset1 @ X39 @ X40 @ X41))),
% 0.54/0.71      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.54/0.71  thf(t72_enumset1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.71     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.54/0.71  thf('6', plain,
% 0.54/0.71      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.54/0.71         ((k3_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45)
% 0.54/0.71           = (k2_enumset1 @ X42 @ X43 @ X44 @ X45))),
% 0.54/0.71      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.54/0.71  thf(t73_enumset1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.54/0.71     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.54/0.71       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.54/0.71  thf('7', plain,
% 0.54/0.71      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.54/0.71         ((k4_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 @ X50)
% 0.54/0.71           = (k3_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50))),
% 0.54/0.71      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.54/0.71  thf(t74_enumset1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.54/0.71     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.54/0.71       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.54/0.71  thf('8', plain,
% 0.54/0.71      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.54/0.71         ((k5_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56)
% 0.54/0.71           = (k4_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56))),
% 0.54/0.71      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.54/0.71  thf(t75_enumset1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.54/0.71     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.54/0.71       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.54/0.71  thf('9', plain,
% 0.54/0.71      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 0.54/0.71         ((k6_enumset1 @ X57 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63)
% 0.54/0.71           = (k5_enumset1 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63))),
% 0.54/0.71      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.54/0.71  thf(t62_enumset1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.54/0.71     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.54/0.71       ( k2_xboole_0 @
% 0.54/0.71         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.54/0.71  thf('10', plain,
% 0.54/0.71      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, 
% 0.54/0.71         X35 : $i]:
% 0.54/0.71         ((k6_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 0.54/0.71           = (k2_xboole_0 @ (k1_tarski @ X28) @ 
% 0.54/0.71              (k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.54/0.71  thf('11', plain,
% 0.54/0.71      (![X3 : $i, X4 : $i]:
% 0.54/0.71         (((X3) = (k1_xboole_0)) | ((k2_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.54/0.71  thf('12', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.54/0.71         (((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.54/0.71            != (k1_xboole_0))
% 0.54/0.71          | ((k1_tarski @ X7) = (k1_xboole_0)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.71  thf(t20_zfmisc_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.54/0.71         ( k1_tarski @ A ) ) <=>
% 0.54/0.71       ( ( A ) != ( B ) ) ))).
% 0.54/0.71  thf('13', plain,
% 0.54/0.71      (![X66 : $i, X67 : $i]:
% 0.54/0.71         (((X67) != (X66))
% 0.54/0.71          | ((k4_xboole_0 @ (k1_tarski @ X67) @ (k1_tarski @ X66))
% 0.54/0.71              != (k1_tarski @ X67)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.54/0.71  thf('14', plain,
% 0.54/0.71      (![X66 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ (k1_tarski @ X66) @ (k1_tarski @ X66))
% 0.54/0.71           != (k1_tarski @ X66))),
% 0.54/0.71      inference('simplify', [status(thm)], ['13'])).
% 0.54/0.71  thf(t92_xboole_1, axiom,
% 0.54/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.54/0.71  thf('15', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.54/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.71  thf(t95_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( k3_xboole_0 @ A @ B ) =
% 0.54/0.71       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.54/0.71  thf('16', plain,
% 0.54/0.71      (![X10 : $i, X11 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ X10 @ X11)
% 0.54/0.71           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 0.54/0.71              (k2_xboole_0 @ X10 @ X11)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.54/0.71  thf('17', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ X0 @ X0)
% 0.54/0.71           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['15', '16'])).
% 0.54/0.71  thf(idempotence_k2_xboole_0, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.54/0.71  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.54/0.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.54/0.71  thf('19', plain,
% 0.54/0.71      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.54/0.71      inference('demod', [status(thm)], ['17', '18'])).
% 0.54/0.71  thf('20', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.54/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.71  thf('21', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.54/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.71  thf(t91_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.54/0.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.54/0.71  thf('22', plain,
% 0.54/0.71      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.54/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.54/0.71           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.54/0.71  thf('23', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.54/0.71           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['21', '22'])).
% 0.54/0.71  thf('24', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['20', '23'])).
% 0.54/0.71  thf(t5_boole, axiom,
% 0.54/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.71  thf('25', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.54/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.71  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.71      inference('demod', [status(thm)], ['24', '25'])).
% 0.54/0.71  thf('27', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.54/0.71      inference('demod', [status(thm)], ['19', '26'])).
% 0.54/0.71  thf(t100_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.71  thf('28', plain,
% 0.54/0.71      (![X1 : $i, X2 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ X1 @ X2)
% 0.54/0.71           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.71  thf('29', plain,
% 0.54/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['27', '28'])).
% 0.54/0.71  thf('30', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.54/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.71  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['29', '30'])).
% 0.54/0.71  thf('32', plain, (![X66 : $i]: ((k1_xboole_0) != (k1_tarski @ X66))),
% 0.54/0.71      inference('demod', [status(thm)], ['14', '31'])).
% 0.54/0.71  thf('33', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.54/0.71         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.54/0.71           != (k1_xboole_0))),
% 0.54/0.71      inference('clc', [status(thm)], ['12', '32'])).
% 0.54/0.71  thf('34', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.54/0.71         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['9', '33'])).
% 0.54/0.71  thf('35', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.71         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['8', '34'])).
% 0.54/0.71  thf('36', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.54/0.71         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['7', '35'])).
% 0.54/0.71  thf('37', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.71         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['6', '36'])).
% 0.54/0.71  thf('38', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.71         ((k1_enumset1 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['5', '37'])).
% 0.54/0.71  thf('39', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['4', '38'])).
% 0.54/0.71  thf('40', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['3', '39'])).
% 0.54/0.71  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.54/0.71  
% 0.54/0.71  % SZS output end Refutation
% 0.54/0.71  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
