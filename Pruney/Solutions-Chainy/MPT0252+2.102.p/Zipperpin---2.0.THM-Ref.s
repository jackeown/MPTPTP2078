%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z60TASULjx

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:30 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 224 expanded)
%              Number of leaves         :   32 (  85 expanded)
%              Depth                    :   18
%              Number of atoms          :  671 (2314 expanded)
%              Number of equality atoms :   51 ( 188 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t47_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t47_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r2_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('6',plain,(
    ~ ( r2_xboole_0 @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('9',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k6_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 ) @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X6 @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('14',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k5_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 )
      = ( k4_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('15',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('17',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k6_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k5_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('20',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k3_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_enumset1 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X24 @ X24 @ X25 @ X26 )
      = ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) )
      = ( k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','26'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X24 @ X24 @ X25 @ X26 )
      = ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X10 @ X9 @ X8 @ X7 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X24 @ X24 @ X25 @ X26 )
      = ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X49 @ X50 ) )
      = ( k2_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X49 @ X50 ) )
      = ( k2_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( r2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','41'])).

thf('43',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['43','46'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ ( k2_tarski @ X51 @ X53 ) @ X52 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('49',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z60TASULjx
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.59/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.83  % Solved by: fo/fo7.sh
% 0.59/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.83  % done 1330 iterations in 0.385s
% 0.59/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.83  % SZS output start Refutation
% 0.59/0.83  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.59/0.83  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.59/0.83                                           $i > $i).
% 0.59/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.83  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.59/0.83  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.59/0.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.83  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.59/0.83  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.59/0.83  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.59/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.83  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.59/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.83  thf(t47_zfmisc_1, conjecture,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.59/0.83       ( r2_hidden @ A @ C ) ))).
% 0.59/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.83    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.83        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.59/0.83          ( r2_hidden @ A @ C ) ) )),
% 0.59/0.83    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.59/0.83  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(t7_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.83  thf('1', plain,
% 0.59/0.83      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.59/0.83      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.59/0.83  thf(d8_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.59/0.83       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.59/0.83  thf('2', plain,
% 0.59/0.83      (![X0 : $i, X2 : $i]:
% 0.59/0.83         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.59/0.83      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.59/0.83  thf('3', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 0.59/0.83          | (r2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.83  thf('4', plain,
% 0.59/0.83      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(t60_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.59/0.83  thf('5', plain,
% 0.59/0.83      (![X3 : $i, X4 : $i]:
% 0.59/0.83         (~ (r1_tarski @ X3 @ X4) | ~ (r2_xboole_0 @ X4 @ X3))),
% 0.59/0.83      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.59/0.83  thf('6', plain,
% 0.59/0.83      (~ (r2_xboole_0 @ sk_C @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.59/0.83      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.83  thf(t69_enumset1, axiom,
% 0.59/0.83    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.83  thf('7', plain, (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.59/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.83  thf(t70_enumset1, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.59/0.83  thf('8', plain,
% 0.59/0.83      (![X22 : $i, X23 : $i]:
% 0.59/0.83         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.59/0.83      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.83  thf('9', plain, (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.59/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.83  thf('10', plain,
% 0.59/0.83      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['8', '9'])).
% 0.59/0.83  thf(t73_enumset1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.59/0.83     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.59/0.83       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.59/0.83  thf('11', plain,
% 0.59/0.83      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.59/0.83         ((k4_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35)
% 0.59/0.83           = (k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35))),
% 0.59/0.83      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.59/0.83  thf(t67_enumset1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.59/0.83     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.59/0.83       ( k2_xboole_0 @
% 0.59/0.83         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.59/0.83  thf('12', plain,
% 0.59/0.83      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, 
% 0.59/0.83         X20 : $i]:
% 0.59/0.83         ((k6_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.59/0.83           = (k2_xboole_0 @ 
% 0.59/0.83              (k4_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18) @ 
% 0.59/0.83              (k2_tarski @ X19 @ X20)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t67_enumset1])).
% 0.59/0.83  thf('13', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.83         ((k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5)
% 0.59/0.83           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.59/0.83              (k2_tarski @ X6 @ X5)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['11', '12'])).
% 0.59/0.83  thf(t74_enumset1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.59/0.83     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.59/0.83       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.59/0.83  thf('14', plain,
% 0.59/0.83      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.59/0.83         ((k5_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41)
% 0.59/0.83           = (k4_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41))),
% 0.59/0.83      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.59/0.83  thf('15', plain,
% 0.59/0.83      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.59/0.83         ((k4_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35)
% 0.59/0.83           = (k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35))),
% 0.59/0.83      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.59/0.83  thf('16', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.83         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.59/0.83           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['14', '15'])).
% 0.59/0.83  thf(t75_enumset1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.59/0.83     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.59/0.83       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.59/0.83  thf('17', plain,
% 0.59/0.83      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.59/0.83         ((k6_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)
% 0.59/0.83           = (k5_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 0.59/0.83      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.59/0.83  thf('18', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.83         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.59/0.83           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.83  thf('19', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2) @ 
% 0.59/0.83           (k2_tarski @ X1 @ X0)) = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['13', '18'])).
% 0.59/0.83  thf(t72_enumset1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.83     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.59/0.83  thf('20', plain,
% 0.59/0.83      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.59/0.83         ((k3_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30)
% 0.59/0.83           = (k2_enumset1 @ X27 @ X28 @ X29 @ X30))),
% 0.59/0.83      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.59/0.83  thf(t71_enumset1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.59/0.83  thf('21', plain,
% 0.59/0.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.83         ((k2_enumset1 @ X24 @ X24 @ X25 @ X26)
% 0.59/0.83           = (k1_enumset1 @ X24 @ X25 @ X26))),
% 0.59/0.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.83  thf('22', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['20', '21'])).
% 0.59/0.83  thf('23', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.59/0.83           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['19', '22'])).
% 0.59/0.83  thf('24', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1))
% 0.59/0.83           = (k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['10', '23'])).
% 0.59/0.83  thf('25', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['20', '21'])).
% 0.59/0.83  thf('26', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1))
% 0.59/0.83           = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.59/0.83      inference('demod', [status(thm)], ['24', '25'])).
% 0.59/0.83  thf('27', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.59/0.83           = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['7', '26'])).
% 0.59/0.83  thf(t41_enumset1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( k2_tarski @ A @ B ) =
% 0.59/0.83       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.59/0.83  thf('28', plain,
% 0.59/0.83      (![X11 : $i, X12 : $i]:
% 0.59/0.83         ((k2_tarski @ X11 @ X12)
% 0.59/0.83           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X12)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.59/0.83  thf('29', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['27', '28'])).
% 0.59/0.83  thf('30', plain,
% 0.59/0.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.83         ((k2_enumset1 @ X24 @ X24 @ X25 @ X26)
% 0.59/0.83           = (k1_enumset1 @ X24 @ X25 @ X26))),
% 0.59/0.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.83  thf(t125_enumset1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.83     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.59/0.83  thf('31', plain,
% 0.59/0.83      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.59/0.83         ((k2_enumset1 @ X10 @ X9 @ X8 @ X7)
% 0.59/0.83           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 0.59/0.83      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.59/0.83  thf('32', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         ((k2_enumset1 @ X0 @ X1 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['30', '31'])).
% 0.59/0.83  thf('33', plain,
% 0.59/0.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.83         ((k2_enumset1 @ X24 @ X24 @ X25 @ X26)
% 0.59/0.83           = (k1_enumset1 @ X24 @ X25 @ X26))),
% 0.59/0.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.83  thf('34', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['32', '33'])).
% 0.59/0.83  thf('35', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['29', '34'])).
% 0.59/0.83  thf('36', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['27', '28'])).
% 0.59/0.83  thf('37', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['35', '36'])).
% 0.59/0.83  thf(l51_zfmisc_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.83  thf('38', plain,
% 0.59/0.83      (![X49 : $i, X50 : $i]:
% 0.59/0.83         ((k3_tarski @ (k2_tarski @ X49 @ X50)) = (k2_xboole_0 @ X49 @ X50))),
% 0.59/0.83      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.59/0.83  thf('39', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['37', '38'])).
% 0.59/0.83  thf('40', plain,
% 0.59/0.83      (![X49 : $i, X50 : $i]:
% 0.59/0.83         ((k3_tarski @ (k2_tarski @ X49 @ X50)) = (k2_xboole_0 @ X49 @ X50))),
% 0.59/0.83      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.59/0.83  thf('41', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['39', '40'])).
% 0.59/0.83  thf('42', plain,
% 0.59/0.83      (~ (r2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.59/0.83      inference('demod', [status(thm)], ['6', '41'])).
% 0.59/0.83  thf('43', plain,
% 0.59/0.83      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['3', '42'])).
% 0.59/0.83  thf('44', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['39', '40'])).
% 0.59/0.83  thf('45', plain,
% 0.59/0.83      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.59/0.83      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.59/0.83  thf('46', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['44', '45'])).
% 0.59/0.83  thf('47', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.59/0.83      inference('sup+', [status(thm)], ['43', '46'])).
% 0.59/0.83  thf(t38_zfmisc_1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.59/0.83       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.59/0.83  thf('48', plain,
% 0.59/0.83      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.59/0.83         ((r2_hidden @ X51 @ X52)
% 0.59/0.83          | ~ (r1_tarski @ (k2_tarski @ X51 @ X53) @ X52))),
% 0.59/0.83      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.59/0.83  thf('49', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.59/0.83      inference('sup-', [status(thm)], ['47', '48'])).
% 0.59/0.83  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.59/0.83  
% 0.59/0.83  % SZS output end Refutation
% 0.59/0.83  
% 0.59/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
