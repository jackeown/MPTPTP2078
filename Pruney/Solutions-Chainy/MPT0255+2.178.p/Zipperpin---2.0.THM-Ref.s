%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MgQsikRGku

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:16 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   75 (  79 expanded)
%              Number of leaves         :   32 (  36 expanded)
%              Depth                    :   16
%              Number of atoms          :  529 ( 552 expanded)
%              Number of equality atoms :   65 (  70 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X26 @ X26 @ X27 @ X28 )
      = ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('8',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k4_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k5_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k4_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('10',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k6_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 )
      = ( k5_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k6_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k5_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k1_tarski @ X7 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('14',plain,(
    ! [X53: $i,X54: $i] :
      ( ( X54 != X53 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X54 ) @ ( k1_tarski @ X53 ) )
       != ( k1_tarski @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('15',plain,(
    ! [X53: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X53 ) @ ( k1_tarski @ X53 ) )
     != ( k1_tarski @ X53 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','27'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X53: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X53 ) ) ),
    inference(demod,[status(thm)],['15','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['13','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','38'])).

thf('40',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MgQsikRGku
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 662 iterations in 0.224s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.46/0.67                                           $i > $i).
% 0.46/0.67  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.67  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.67  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(t50_zfmisc_1, conjecture,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.67        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t15_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.67       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      (![X3 : $i, X4 : $i]:
% 0.46/0.67         (((X3) = (k1_xboole_0)) | ((k2_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.67        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.67  thf('3', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['2'])).
% 0.46/0.67  thf(t71_enumset1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.67         ((k2_enumset1 @ X26 @ X26 @ X27 @ X28)
% 0.46/0.67           = (k1_enumset1 @ X26 @ X27 @ X28))),
% 0.46/0.67      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.46/0.67  thf(t70_enumset1, axiom,
% 0.46/0.67    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      (![X24 : $i, X25 : $i]:
% 0.46/0.67         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.46/0.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['4', '5'])).
% 0.46/0.67  thf(t72_enumset1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.46/0.67         ((k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32)
% 0.46/0.67           = (k2_enumset1 @ X29 @ X30 @ X31 @ X32))),
% 0.46/0.67      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.46/0.67  thf(t73_enumset1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.67     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.46/0.67       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.46/0.67         ((k4_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 @ X37)
% 0.46/0.67           = (k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 0.46/0.67      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.46/0.67  thf(t74_enumset1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.67     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.46/0.67       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.46/0.67         ((k5_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43)
% 0.46/0.67           = (k4_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43))),
% 0.46/0.67      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.46/0.67  thf(t75_enumset1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.46/0.67     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.46/0.67       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.46/0.67         ((k6_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50)
% 0.46/0.67           = (k5_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50))),
% 0.46/0.67      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.46/0.67  thf(t62_enumset1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.46/0.67     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.46/0.67       ( k2_xboole_0 @
% 0.46/0.67         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, 
% 0.46/0.67         X22 : $i]:
% 0.46/0.67         ((k6_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.46/0.67           = (k2_xboole_0 @ (k1_tarski @ X15) @ 
% 0.46/0.67              (k5_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (![X3 : $i, X4 : $i]:
% 0.46/0.67         (((X3) = (k1_xboole_0)) | ((k2_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.46/0.67  thf('13', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.67         (((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.46/0.67            != (k1_xboole_0))
% 0.46/0.67          | ((k1_tarski @ X7) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.67  thf(t20_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.46/0.67         ( k1_tarski @ A ) ) <=>
% 0.46/0.67       ( ( A ) != ( B ) ) ))).
% 0.46/0.67  thf('14', plain,
% 0.46/0.67      (![X53 : $i, X54 : $i]:
% 0.46/0.67         (((X54) != (X53))
% 0.46/0.67          | ((k4_xboole_0 @ (k1_tarski @ X54) @ (k1_tarski @ X53))
% 0.46/0.67              != (k1_tarski @ X54)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      (![X53 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k1_tarski @ X53) @ (k1_tarski @ X53))
% 0.46/0.67           != (k1_tarski @ X53))),
% 0.46/0.67      inference('simplify', [status(thm)], ['14'])).
% 0.46/0.67  thf(t92_xboole_1, axiom,
% 0.46/0.67    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.67  thf('16', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.67  thf(t95_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( k3_xboole_0 @ A @ B ) =
% 0.46/0.67       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      (![X10 : $i, X11 : $i]:
% 0.46/0.67         ((k3_xboole_0 @ X10 @ X11)
% 0.46/0.67           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 0.46/0.67              (k2_xboole_0 @ X10 @ X11)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((k3_xboole_0 @ X0 @ X0)
% 0.46/0.67           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.67  thf(idempotence_k2_xboole_0, axiom,
% 0.46/0.67    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.67  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.67      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.46/0.67  thf('20', plain,
% 0.46/0.67      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.67      inference('demod', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf('21', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.67  thf('22', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.67  thf(t91_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.67       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.46/0.67  thf('23', plain,
% 0.46/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.46/0.67           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.67  thf('24', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.67           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['22', '23'])).
% 0.46/0.67  thf('25', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['21', '24'])).
% 0.46/0.67  thf(t5_boole, axiom,
% 0.46/0.67    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.67  thf('26', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.46/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.67  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.67      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.67  thf('28', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.67      inference('demod', [status(thm)], ['20', '27'])).
% 0.46/0.67  thf(t100_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      (![X1 : $i, X2 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ X1 @ X2)
% 0.46/0.67           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.67  thf('31', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.67  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.67  thf('33', plain, (![X53 : $i]: ((k1_xboole_0) != (k1_tarski @ X53))),
% 0.46/0.67      inference('demod', [status(thm)], ['15', '32'])).
% 0.46/0.67  thf('34', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.67         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.46/0.67           != (k1_xboole_0))),
% 0.46/0.67      inference('clc', [status(thm)], ['13', '33'])).
% 0.46/0.67  thf('35', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.67         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['10', '34'])).
% 0.46/0.67  thf('36', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.67         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['9', '35'])).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.67         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['8', '36'])).
% 0.46/0.67  thf('38', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['7', '37'])).
% 0.46/0.67  thf('39', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['6', '38'])).
% 0.46/0.67  thf('40', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['3', '39'])).
% 0.46/0.67  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.53/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
