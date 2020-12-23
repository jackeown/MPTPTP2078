%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rDMu5UQ2wG

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:55 EST 2020

% Result     : Theorem 12.49s
% Output     : Refutation 12.49s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 113 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  610 ( 863 expanded)
%              Number of equality atoms :   65 ( 114 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('1',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k6_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('4',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k6_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ sk_A )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k5_xboole_0 @ k1_xboole_0 @ ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('13',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k6_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['1','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ ( k5_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','20'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('22',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k5_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('23',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k4_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('24',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf('31',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22','23','24','29','30'])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('33',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53 != X52 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X53 ) @ ( k1_tarski @ X52 ) )
       != ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('34',plain,(
    ! [X52: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X52 ) @ ( k1_tarski @ X52 ) )
     != ( k1_tarski @ X52 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf('38',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rDMu5UQ2wG
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 12.49/12.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.49/12.66  % Solved by: fo/fo7.sh
% 12.49/12.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.49/12.66  % done 8618 iterations in 12.205s
% 12.49/12.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.49/12.66  % SZS output start Refutation
% 12.49/12.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 12.49/12.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.49/12.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 12.49/12.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 12.49/12.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 12.49/12.66  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 12.49/12.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 12.49/12.66  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 12.49/12.66  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 12.49/12.66  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 12.49/12.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 12.49/12.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 12.49/12.66  thf(sk_A_type, type, sk_A: $i).
% 12.49/12.66  thf(sk_B_type, type, sk_B: $i).
% 12.49/12.66  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 12.49/12.66                                           $i > $i).
% 12.49/12.66  thf(t92_xboole_1, axiom,
% 12.49/12.66    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 12.49/12.66  thf('0', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 12.49/12.66      inference('cnf', [status(esa)], [t92_xboole_1])).
% 12.49/12.66  thf(t75_enumset1, axiom,
% 12.49/12.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 12.49/12.66     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 12.49/12.66       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 12.49/12.66  thf('1', plain,
% 12.49/12.66      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 12.49/12.66         ((k6_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 12.49/12.66           = (k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 12.49/12.66      inference('cnf', [status(esa)], [t75_enumset1])).
% 12.49/12.66  thf(t49_zfmisc_1, conjecture,
% 12.49/12.66    (![A:$i,B:$i]:
% 12.49/12.66     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 12.49/12.66  thf(zf_stmt_0, negated_conjecture,
% 12.49/12.66    (~( ![A:$i,B:$i]:
% 12.49/12.66        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 12.49/12.66    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 12.49/12.66  thf('2', plain,
% 12.49/12.66      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 12.49/12.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.49/12.66  thf(t15_xboole_1, axiom,
% 12.49/12.66    (![A:$i,B:$i]:
% 12.49/12.66     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 12.49/12.66       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 12.49/12.66  thf('3', plain,
% 12.49/12.66      (![X2 : $i, X3 : $i]:
% 12.49/12.66         (((X2) = (k1_xboole_0)) | ((k2_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 12.49/12.66      inference('cnf', [status(esa)], [t15_xboole_1])).
% 12.49/12.66  thf('4', plain,
% 12.49/12.66      ((((k1_xboole_0) != (k1_xboole_0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 12.49/12.66      inference('sup-', [status(thm)], ['2', '3'])).
% 12.49/12.66  thf('5', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 12.49/12.66      inference('simplify', [status(thm)], ['4'])).
% 12.49/12.66  thf(t68_enumset1, axiom,
% 12.49/12.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 12.49/12.66     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 12.49/12.66       ( k2_xboole_0 @
% 12.49/12.66         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 12.49/12.66  thf('6', plain,
% 12.49/12.66      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 12.49/12.66         X21 : $i]:
% 12.49/12.66         ((k6_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 12.49/12.66           = (k2_xboole_0 @ 
% 12.49/12.66              (k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20) @ 
% 12.49/12.66              (k1_tarski @ X21)))),
% 12.49/12.66      inference('cnf', [status(esa)], [t68_enumset1])).
% 12.49/12.66  thf('7', plain,
% 12.49/12.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 12.49/12.66         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ sk_A)
% 12.49/12.66           = (k2_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 12.49/12.66              k1_xboole_0))),
% 12.49/12.66      inference('sup+', [status(thm)], ['5', '6'])).
% 12.49/12.66  thf(t95_xboole_1, axiom,
% 12.49/12.66    (![A:$i,B:$i]:
% 12.49/12.66     ( ( k3_xboole_0 @ A @ B ) =
% 12.49/12.66       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 12.49/12.66  thf('8', plain,
% 12.49/12.66      (![X9 : $i, X10 : $i]:
% 12.49/12.66         ((k3_xboole_0 @ X9 @ X10)
% 12.49/12.66           = (k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ (k2_xboole_0 @ X9 @ X10)))),
% 12.49/12.66      inference('cnf', [status(esa)], [t95_xboole_1])).
% 12.49/12.66  thf(t91_xboole_1, axiom,
% 12.49/12.66    (![A:$i,B:$i,C:$i]:
% 12.49/12.66     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 12.49/12.66       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 12.49/12.66  thf('9', plain,
% 12.49/12.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 12.49/12.66         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 12.49/12.66           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 12.49/12.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 12.49/12.66  thf('10', plain,
% 12.49/12.66      (![X9 : $i, X10 : $i]:
% 12.49/12.66         ((k3_xboole_0 @ X9 @ X10)
% 12.49/12.66           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ (k2_xboole_0 @ X9 @ X10))))),
% 12.49/12.66      inference('demod', [status(thm)], ['8', '9'])).
% 12.49/12.66  thf('11', plain,
% 12.49/12.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 12.49/12.66         ((k3_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 12.49/12.66           k1_xboole_0)
% 12.49/12.66           = (k5_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 12.49/12.66              (k5_xboole_0 @ k1_xboole_0 @ 
% 12.49/12.66               (k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ sk_A))))),
% 12.49/12.66      inference('sup+', [status(thm)], ['7', '10'])).
% 12.49/12.66  thf('12', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 12.49/12.66      inference('cnf', [status(esa)], [t92_xboole_1])).
% 12.49/12.66  thf('13', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 12.49/12.66      inference('cnf', [status(esa)], [t92_xboole_1])).
% 12.49/12.66  thf('14', plain,
% 12.49/12.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 12.49/12.66         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 12.49/12.66           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 12.49/12.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 12.49/12.66  thf('15', plain,
% 12.49/12.66      (![X0 : $i, X1 : $i]:
% 12.49/12.66         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 12.49/12.66           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 12.49/12.66      inference('sup+', [status(thm)], ['13', '14'])).
% 12.49/12.66  thf('16', plain,
% 12.49/12.66      (![X0 : $i]:
% 12.49/12.66         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 12.49/12.66      inference('sup+', [status(thm)], ['12', '15'])).
% 12.49/12.66  thf(t5_boole, axiom,
% 12.49/12.66    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 12.49/12.66  thf('17', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 12.49/12.66      inference('cnf', [status(esa)], [t5_boole])).
% 12.49/12.66  thf('18', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 12.49/12.66      inference('demod', [status(thm)], ['16', '17'])).
% 12.49/12.66  thf('19', plain,
% 12.49/12.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 12.49/12.66         ((k3_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 12.49/12.66           k1_xboole_0)
% 12.49/12.66           = (k5_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 12.49/12.66              (k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ sk_A)))),
% 12.49/12.66      inference('demod', [status(thm)], ['11', '18'])).
% 12.49/12.66  thf('20', plain,
% 12.49/12.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 12.49/12.66         ((k3_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 12.49/12.66           k1_xboole_0)
% 12.49/12.66           = (k5_xboole_0 @ 
% 12.49/12.66              (k6_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 12.49/12.66              (k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ sk_A)))),
% 12.49/12.66      inference('sup+', [status(thm)], ['1', '19'])).
% 12.49/12.66  thf('21', plain,
% 12.49/12.66      (((k3_xboole_0 @ 
% 12.49/12.66         (k5_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A) @ 
% 12.49/12.66         k1_xboole_0) = (k1_xboole_0))),
% 12.49/12.66      inference('sup+', [status(thm)], ['0', '20'])).
% 12.49/12.66  thf(t74_enumset1, axiom,
% 12.49/12.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 12.49/12.66     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 12.49/12.66       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 12.49/12.66  thf('22', plain,
% 12.49/12.66      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 12.49/12.66         ((k5_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 12.49/12.66           = (k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 12.49/12.66      inference('cnf', [status(esa)], [t74_enumset1])).
% 12.49/12.66  thf(t73_enumset1, axiom,
% 12.49/12.66    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 12.49/12.66     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 12.49/12.66       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 12.49/12.66  thf('23', plain,
% 12.49/12.66      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 12.49/12.66         ((k4_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36)
% 12.49/12.66           = (k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 12.49/12.66      inference('cnf', [status(esa)], [t73_enumset1])).
% 12.49/12.66  thf(t72_enumset1, axiom,
% 12.49/12.66    (![A:$i,B:$i,C:$i,D:$i]:
% 12.49/12.66     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 12.49/12.66  thf('24', plain,
% 12.49/12.66      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 12.49/12.66         ((k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31)
% 12.49/12.66           = (k2_enumset1 @ X28 @ X29 @ X30 @ X31))),
% 12.49/12.66      inference('cnf', [status(esa)], [t72_enumset1])).
% 12.49/12.66  thf(t71_enumset1, axiom,
% 12.49/12.66    (![A:$i,B:$i,C:$i]:
% 12.49/12.66     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 12.49/12.66  thf('25', plain,
% 12.49/12.66      (![X25 : $i, X26 : $i, X27 : $i]:
% 12.49/12.66         ((k2_enumset1 @ X25 @ X25 @ X26 @ X27)
% 12.49/12.66           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 12.49/12.66      inference('cnf', [status(esa)], [t71_enumset1])).
% 12.49/12.66  thf(t70_enumset1, axiom,
% 12.49/12.66    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 12.49/12.66  thf('26', plain,
% 12.49/12.66      (![X23 : $i, X24 : $i]:
% 12.49/12.66         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 12.49/12.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 12.49/12.66  thf('27', plain,
% 12.49/12.66      (![X0 : $i, X1 : $i]:
% 12.49/12.66         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 12.49/12.66      inference('sup+', [status(thm)], ['25', '26'])).
% 12.49/12.66  thf(t69_enumset1, axiom,
% 12.49/12.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 12.49/12.66  thf('28', plain,
% 12.49/12.66      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 12.49/12.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 12.49/12.66  thf('29', plain,
% 12.49/12.66      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 12.49/12.66      inference('sup+', [status(thm)], ['27', '28'])).
% 12.49/12.66  thf('30', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 12.49/12.66      inference('simplify', [status(thm)], ['4'])).
% 12.49/12.66  thf('31', plain,
% 12.49/12.66      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 12.49/12.66      inference('demod', [status(thm)], ['21', '22', '23', '24', '29', '30'])).
% 12.49/12.66  thf('32', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 12.49/12.66      inference('simplify', [status(thm)], ['4'])).
% 12.49/12.66  thf(t20_zfmisc_1, axiom,
% 12.49/12.66    (![A:$i,B:$i]:
% 12.49/12.66     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 12.49/12.66         ( k1_tarski @ A ) ) <=>
% 12.49/12.66       ( ( A ) != ( B ) ) ))).
% 12.49/12.66  thf('33', plain,
% 12.49/12.66      (![X52 : $i, X53 : $i]:
% 12.49/12.66         (((X53) != (X52))
% 12.49/12.66          | ((k4_xboole_0 @ (k1_tarski @ X53) @ (k1_tarski @ X52))
% 12.49/12.66              != (k1_tarski @ X53)))),
% 12.49/12.66      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 12.49/12.66  thf('34', plain,
% 12.49/12.66      (![X52 : $i]:
% 12.49/12.66         ((k4_xboole_0 @ (k1_tarski @ X52) @ (k1_tarski @ X52))
% 12.49/12.66           != (k1_tarski @ X52))),
% 12.49/12.66      inference('simplify', [status(thm)], ['33'])).
% 12.49/12.66  thf('35', plain,
% 12.49/12.66      (((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 12.49/12.66      inference('sup-', [status(thm)], ['32', '34'])).
% 12.49/12.66  thf('36', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 12.49/12.66      inference('simplify', [status(thm)], ['4'])).
% 12.49/12.66  thf('37', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 12.49/12.66      inference('simplify', [status(thm)], ['4'])).
% 12.49/12.66  thf('38', plain,
% 12.49/12.66      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 12.49/12.66      inference('demod', [status(thm)], ['35', '36', '37'])).
% 12.49/12.66  thf('39', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 12.49/12.66      inference('demod', [status(thm)], ['16', '17'])).
% 12.49/12.66  thf(t100_xboole_1, axiom,
% 12.49/12.66    (![A:$i,B:$i]:
% 12.49/12.66     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 12.49/12.66  thf('40', plain,
% 12.49/12.66      (![X0 : $i, X1 : $i]:
% 12.49/12.66         ((k4_xboole_0 @ X0 @ X1)
% 12.49/12.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 12.49/12.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 12.49/12.66  thf('41', plain,
% 12.49/12.66      (![X0 : $i]:
% 12.49/12.66         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 12.49/12.66      inference('sup+', [status(thm)], ['39', '40'])).
% 12.49/12.66  thf('42', plain,
% 12.49/12.66      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 12.49/12.66      inference('demod', [status(thm)], ['38', '41'])).
% 12.49/12.66  thf('43', plain, ($false),
% 12.49/12.66      inference('simplify_reflect-', [status(thm)], ['31', '42'])).
% 12.49/12.66  
% 12.49/12.66  % SZS output end Refutation
% 12.49/12.66  
% 12.49/12.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
