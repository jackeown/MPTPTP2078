%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Jkk94nEAWy

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:04 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 138 expanded)
%              Number of leaves         :   25 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  815 (1631 expanded)
%              Number of equality atoms :   59 ( 124 expanded)
%              Maximal formula depth    :   21 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k6_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) @ ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('7',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_tarski @ ( k1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) )
      = ( k6_enumset1 @ X3 @ X2 @ X1 @ X0 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t134_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) @ ( k1_tarski @ I ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k7_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k6_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t134_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k7_enumset1 @ X3 @ X2 @ X1 @ X0 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k3_tarski @ ( k1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_tarski @ ( k1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) )
      = ( k6_enumset1 @ X3 @ X2 @ X1 @ X0 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_tarski @ ( k1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) )
      = ( k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('16',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k6_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k5_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_tarski @ ( k1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) )
      = ( k5_enumset1 @ X2 @ X1 @ X0 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('18',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k5_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k4_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) )
      = ( k4_enumset1 @ X1 @ X0 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('20',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t131_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_enumset1 @ F @ G @ H @ I ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k7_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) @ ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t131_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k7_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X8 @ X7 @ X6 @ X5 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X8 @ X7 @ X6 @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k7_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k3_tarski @ ( k1_tarski @ ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ) @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) )
      = ( k4_enumset1 @ X1 @ X0 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('25',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('26',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ ( k1_enumset1 @ X0 @ X0 @ X0 ) ) )
      = ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k6_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) @ ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k6_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k5_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k5_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k4_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k7_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k4_enumset1 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','30','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_tarski @ ( k1_tarski @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      = ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','37'])).

thf('39',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ ( k1_enumset1 @ X0 @ X0 @ X0 ) ) )
      = ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','42'])).

thf('44',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('45',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','43','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Jkk94nEAWy
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:35:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.98  % Solved by: fo/fo7.sh
% 0.75/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.98  % done 774 iterations in 0.519s
% 0.75/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.98  % SZS output start Refutation
% 0.75/0.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.98  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.75/0.98  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.75/0.98  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.75/0.98  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.98  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.75/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.75/0.98  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.75/0.98  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.75/0.98                                           $i > $i > $i).
% 0.75/0.98  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.75/0.98                                           $i > $i).
% 0.75/0.98  thf(t32_zfmisc_1, conjecture,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.75/0.98       ( k2_tarski @ A @ B ) ))).
% 0.75/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.98    (~( ![A:$i,B:$i]:
% 0.75/0.98        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.75/0.98          ( k2_tarski @ A @ B ) ) )),
% 0.75/0.98    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.75/0.98  thf('0', plain,
% 0.75/0.98      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.75/0.98         != (k2_tarski @ sk_A @ sk_B))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(l51_zfmisc_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.98  thf('1', plain,
% 0.75/0.98      (![X56 : $i, X57 : $i]:
% 0.75/0.98         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 0.75/0.98      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.75/0.98  thf('2', plain,
% 0.75/0.98      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.75/0.98         != (k2_tarski @ sk_A @ sk_B))),
% 0.75/0.98      inference('demod', [status(thm)], ['0', '1'])).
% 0.75/0.98  thf(t70_enumset1, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.75/0.98  thf('3', plain,
% 0.75/0.98      (![X29 : $i, X30 : $i]:
% 0.75/0.98         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.75/0.98      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.98  thf(t69_enumset1, axiom,
% 0.75/0.98    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.75/0.98  thf('4', plain, (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.75/0.98      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.98  thf('5', plain,
% 0.75/0.98      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['3', '4'])).
% 0.75/0.98  thf(l75_enumset1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.75/0.98     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.75/0.98       ( k2_xboole_0 @
% 0.75/0.98         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.75/0.98  thf('6', plain,
% 0.75/0.98      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.75/0.98         ((k6_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 0.75/0.98           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X3 @ X4 @ X5) @ 
% 0.75/0.98              (k2_enumset1 @ X6 @ X7 @ X8 @ X9)))),
% 0.75/0.98      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.75/0.98  thf('7', plain, (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.75/0.98      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.98  thf('8', plain,
% 0.75/0.98      (![X56 : $i, X57 : $i]:
% 0.75/0.98         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 0.75/0.98      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.75/0.98  thf('9', plain,
% 0.75/0.98      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['7', '8'])).
% 0.75/0.98  thf('10', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.98         ((k3_tarski @ (k1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))
% 0.75/0.98           = (k6_enumset1 @ X3 @ X2 @ X1 @ X0 @ X3 @ X2 @ X1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['6', '9'])).
% 0.75/0.98  thf(t134_enumset1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.75/0.98     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.75/0.98       ( k2_xboole_0 @
% 0.75/0.98         ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) @ ( k1_tarski @ I ) ) ))).
% 0.75/0.98  thf('11', plain,
% 0.75/0.98      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.75/0.98         X26 : $i, X27 : $i]:
% 0.75/0.98         ((k7_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.75/0.98           = (k2_xboole_0 @ 
% 0.75/0.98              (k6_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26) @ 
% 0.75/0.98              (k1_tarski @ X27)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t134_enumset1])).
% 0.75/0.98  thf('12', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.98         ((k7_enumset1 @ X3 @ X2 @ X1 @ X0 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.75/0.98           = (k2_xboole_0 @ 
% 0.75/0.98              (k3_tarski @ (k1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))) @ 
% 0.75/0.98              (k1_tarski @ X4)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['10', '11'])).
% 0.75/0.98  thf(t71_enumset1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.75/0.98  thf('13', plain,
% 0.75/0.98      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.75/0.98         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 0.75/0.98           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 0.75/0.98      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.75/0.98  thf('14', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.98         ((k3_tarski @ (k1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))
% 0.75/0.98           = (k6_enumset1 @ X3 @ X2 @ X1 @ X0 @ X3 @ X2 @ X1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['6', '9'])).
% 0.75/0.98  thf('15', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((k3_tarski @ (k1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0)))
% 0.75/0.98           = (k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X2 @ X2 @ X1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['13', '14'])).
% 0.75/0.98  thf(t75_enumset1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.75/0.98     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.75/0.98       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.75/0.98  thf('16', plain,
% 0.75/0.98      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.75/0.98         ((k6_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 0.75/0.98           = (k5_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 0.75/0.98      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.75/0.98  thf('17', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((k3_tarski @ (k1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0)))
% 0.75/0.98           = (k5_enumset1 @ X2 @ X1 @ X0 @ X2 @ X2 @ X1 @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['15', '16'])).
% 0.75/0.98  thf(t74_enumset1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.75/0.98     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.75/0.98       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.75/0.98  thf('18', plain,
% 0.75/0.98      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.75/0.98         ((k5_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)
% 0.75/0.98           = (k4_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 0.75/0.98      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.75/0.98  thf('19', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k3_tarski @ (k1_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)))
% 0.75/0.98           = (k4_enumset1 @ X1 @ X0 @ X1 @ X1 @ X1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['17', '18'])).
% 0.75/0.98  thf(t73_enumset1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.75/0.98     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.75/0.98       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.75/0.98  thf('20', plain,
% 0.75/0.98      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.75/0.98         ((k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.75/0.98           = (k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 0.75/0.98      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.75/0.98  thf(t131_enumset1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.75/0.98     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.75/0.98       ( k2_xboole_0 @
% 0.75/0.98         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_enumset1 @ F @ G @ H @ I ) ) ))).
% 0.75/0.98  thf('21', plain,
% 0.75/0.98      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, 
% 0.75/0.98         X17 : $i, X18 : $i]:
% 0.75/0.98         ((k7_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.75/0.98           = (k2_xboole_0 @ (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14) @ 
% 0.75/0.98              (k2_enumset1 @ X15 @ X16 @ X17 @ X18)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t131_enumset1])).
% 0.75/0.98  thf('22', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.75/0.98         X7 : $i, X8 : $i]:
% 0.75/0.98         ((k7_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X8 @ X7 @ X6 @ X5)
% 0.75/0.98           = (k2_xboole_0 @ (k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.75/0.98              (k2_enumset1 @ X8 @ X7 @ X6 @ X5)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['20', '21'])).
% 0.75/0.98  thf('23', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.98         ((k7_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1)
% 0.75/0.98           = (k2_xboole_0 @ 
% 0.75/0.98              (k3_tarski @ (k1_tarski @ (k1_enumset1 @ X0 @ X0 @ X0))) @ 
% 0.75/0.98              (k2_enumset1 @ X4 @ X3 @ X2 @ X1)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['19', '22'])).
% 0.75/0.98  thf('24', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k3_tarski @ (k1_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)))
% 0.75/0.98           = (k4_enumset1 @ X1 @ X0 @ X1 @ X1 @ X1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['17', '18'])).
% 0.75/0.98  thf(t72_enumset1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.98     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.75/0.98  thf('25', plain,
% 0.75/0.98      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.75/0.98         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 0.75/0.98           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 0.75/0.98      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.75/0.98  thf('26', plain,
% 0.75/0.98      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.75/0.98         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 0.75/0.98           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 0.75/0.98      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.75/0.98  thf('27', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['25', '26'])).
% 0.75/0.98  thf('28', plain,
% 0.75/0.98      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.75/0.98         ((k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.75/0.98           = (k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 0.75/0.98      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.75/0.98  thf('29', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 0.75/0.98           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['27', '28'])).
% 0.75/0.98  thf('30', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((k3_tarski @ (k1_tarski @ (k1_enumset1 @ X0 @ X0 @ X0)))
% 0.75/0.98           = (k1_enumset1 @ X0 @ X0 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['24', '29'])).
% 0.75/0.98  thf('31', plain,
% 0.75/0.98      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.75/0.98         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 0.75/0.98           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 0.75/0.98      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.75/0.98  thf('32', plain,
% 0.75/0.98      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.75/0.98         ((k6_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 0.75/0.98           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X3 @ X4 @ X5) @ 
% 0.75/0.98              (k2_enumset1 @ X6 @ X7 @ X8 @ X9)))),
% 0.75/0.98      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.75/0.98  thf('33', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.75/0.98         ((k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.75/0.98           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.75/0.98              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['31', '32'])).
% 0.75/0.98  thf('34', plain,
% 0.75/0.98      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.75/0.98         ((k6_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 0.75/0.98           = (k5_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 0.75/0.98      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.75/0.98  thf('35', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.75/0.98         ((k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.75/0.98           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.75/0.98              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 0.75/0.98      inference('demod', [status(thm)], ['33', '34'])).
% 0.75/0.98  thf('36', plain,
% 0.75/0.98      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.75/0.98         ((k5_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)
% 0.75/0.98           = (k4_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 0.75/0.98      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.75/0.98  thf('37', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.98         ((k7_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1)
% 0.75/0.98           = (k4_enumset1 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1))),
% 0.75/0.98      inference('demod', [status(thm)], ['23', '30', '35', '36'])).
% 0.75/0.98  thf('38', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ 
% 0.75/0.98           (k3_tarski @ (k1_tarski @ (k2_enumset1 @ X1 @ X1 @ X1 @ X1))) @ 
% 0.75/0.98           (k1_tarski @ X0)) = (k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['12', '37'])).
% 0.75/0.98  thf('39', plain,
% 0.75/0.98      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.75/0.98         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 0.75/0.98           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 0.75/0.98      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.75/0.98  thf('40', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((k3_tarski @ (k1_tarski @ (k1_enumset1 @ X0 @ X0 @ X0)))
% 0.75/0.98           = (k1_enumset1 @ X0 @ X0 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['24', '29'])).
% 0.75/0.98  thf('41', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 0.75/0.98           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['27', '28'])).
% 0.75/0.98  thf('42', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X1) @ (k1_tarski @ X0))
% 0.75/0.98           = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.75/0.98  thf('43', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.75/0.98           = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.75/0.98      inference('sup+', [status(thm)], ['5', '42'])).
% 0.75/0.98  thf('44', plain,
% 0.75/0.98      (![X29 : $i, X30 : $i]:
% 0.75/0.98         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.75/0.98      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.98  thf('45', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.75/0.98      inference('demod', [status(thm)], ['2', '43', '44'])).
% 0.75/0.98  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.75/0.98  
% 0.75/0.98  % SZS output end Refutation
% 0.75/0.98  
% 0.75/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
