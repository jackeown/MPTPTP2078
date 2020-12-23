%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.utDRurSwee

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:32 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 107 expanded)
%              Number of leaves         :   25 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  765 (1133 expanded)
%              Number of equality atoms :   62 (  94 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X8 @ X6 @ X7 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X8 @ X6 @ X7 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('3',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k2_enumset1 @ X63 @ X63 @ X64 @ X65 )
      = ( k1_enumset1 @ X63 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k1_enumset1 @ X61 @ X61 @ X62 )
      = ( k2_tarski @ X61 @ X62 ) ) ),
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
    ! [X66: $i,X67: $i,X68: $i,X69: $i] :
      ( ( k3_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69 )
      = ( k2_enumset1 @ X66 @ X67 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 ) @ ( k2_tarski @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('11',plain,(
    ! [X75: $i,X76: $i,X77: $i,X78: $i,X79: $i,X80: $i] :
      ( ( k5_enumset1 @ X75 @ X75 @ X76 @ X77 @ X78 @ X79 @ X80 )
      = ( k4_enumset1 @ X75 @ X76 @ X77 @ X78 @ X79 @ X80 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('12',plain,(
    ! [X70: $i,X71: $i,X72: $i,X73: $i,X74: $i] :
      ( ( k4_enumset1 @ X70 @ X70 @ X71 @ X72 @ X73 @ X74 )
      = ( k3_enumset1 @ X70 @ X71 @ X72 @ X73 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X66: $i,X67: $i,X68: $i,X69: $i] :
      ( ( k3_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69 )
      = ( k2_enumset1 @ X66 @ X67 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['10','13','14'])).

thf('16',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','15'])).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X8 @ X6 @ X7 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('18',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k1_enumset1 @ X61 @ X61 @ X62 )
      = ( k2_tarski @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k1_enumset1 @ X11 @ X10 @ X9 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X8 @ X6 @ X7 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X60: $i] :
      ( ( k2_tarski @ X60 @ X60 )
      = ( k1_tarski @ X60 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X66: $i,X67: $i,X68: $i,X69: $i] :
      ( ( k3_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69 )
      = ( k2_enumset1 @ X66 @ X67 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('27',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k6_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 ) @ ( k1_enumset1 @ X49 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X6 @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('29',plain,(
    ! [X81: $i,X82: $i,X83: $i,X84: $i,X85: $i,X86: $i,X87: $i] :
      ( ( k6_enumset1 @ X81 @ X81 @ X82 @ X83 @ X84 @ X85 @ X86 @ X87 )
      = ( k5_enumset1 @ X81 @ X82 @ X83 @ X84 @ X85 @ X86 @ X87 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X6 @ X5 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('33',plain,(
    ! [X66: $i,X67: $i,X68: $i,X69: $i] :
      ( ( k3_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69 )
      = ( k2_enumset1 @ X66 @ X67 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('41',plain,(
    ! [X66: $i,X67: $i,X68: $i,X69: $i] :
      ( ( k3_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69 )
      = ( k2_enumset1 @ X66 @ X67 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k2_enumset1 @ X63 @ X63 @ X64 @ X65 )
      = ( k1_enumset1 @ X63 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','44'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('46',plain,(
    ! [X88: $i,X89: $i,X90: $i] :
      ( ( k1_enumset1 @ X88 @ X90 @ X89 )
      = ( k1_enumset1 @ X88 @ X89 @ X90 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('47',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['16','45','46'])).

thf('48',plain,(
    $false ),
    inference(simplify,[status(thm)],['47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.utDRurSwee
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:52:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.81/1.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.81/1.00  % Solved by: fo/fo7.sh
% 0.81/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.00  % done 1099 iterations in 0.550s
% 0.81/1.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.81/1.00  % SZS output start Refutation
% 0.81/1.00  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.81/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.81/1.00  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.81/1.00  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.81/1.00  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.81/1.00  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.81/1.00                                           $i > $i).
% 0.81/1.00  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.81/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.00  thf(sk_C_type, type, sk_C: $i).
% 0.81/1.00  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.81/1.00  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.81/1.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.81/1.00  thf(t137_enumset1, conjecture,
% 0.81/1.00    (![A:$i,B:$i,C:$i]:
% 0.81/1.00     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.81/1.00       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.81/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.81/1.00    (~( ![A:$i,B:$i,C:$i]:
% 0.81/1.00        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.81/1.00          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.81/1.00    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.81/1.00  thf('0', plain,
% 0.81/1.00      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.81/1.00         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.81/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.00  thf(t100_enumset1, axiom,
% 0.81/1.00    (![A:$i,B:$i,C:$i]:
% 0.81/1.00     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 0.81/1.00  thf('1', plain,
% 0.81/1.00      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.81/1.00         ((k1_enumset1 @ X8 @ X6 @ X7) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.81/1.00      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.81/1.00  thf('2', plain,
% 0.81/1.00      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.81/1.00         ((k1_enumset1 @ X8 @ X6 @ X7) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.81/1.00      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.81/1.00  thf('3', plain,
% 0.81/1.00      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.81/1.00         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.81/1.00      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.81/1.00  thf(t71_enumset1, axiom,
% 0.81/1.00    (![A:$i,B:$i,C:$i]:
% 0.81/1.00     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.81/1.00  thf('4', plain,
% 0.81/1.00      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.81/1.00         ((k2_enumset1 @ X63 @ X63 @ X64 @ X65)
% 0.81/1.00           = (k1_enumset1 @ X63 @ X64 @ X65))),
% 0.81/1.00      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.81/1.00  thf(t70_enumset1, axiom,
% 0.81/1.00    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.81/1.00  thf('5', plain,
% 0.81/1.00      (![X61 : $i, X62 : $i]:
% 0.81/1.00         ((k1_enumset1 @ X61 @ X61 @ X62) = (k2_tarski @ X61 @ X62))),
% 0.81/1.00      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.81/1.00  thf('6', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i]:
% 0.81/1.00         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.81/1.00      inference('sup+', [status(thm)], ['4', '5'])).
% 0.81/1.00  thf(t72_enumset1, axiom,
% 0.81/1.00    (![A:$i,B:$i,C:$i,D:$i]:
% 0.81/1.00     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.81/1.00  thf('7', plain,
% 0.81/1.00      (![X66 : $i, X67 : $i, X68 : $i, X69 : $i]:
% 0.81/1.00         ((k3_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69)
% 0.81/1.00           = (k2_enumset1 @ X66 @ X67 @ X68 @ X69))),
% 0.81/1.00      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.81/1.00  thf(t60_enumset1, axiom,
% 0.81/1.00    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.81/1.00     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.81/1.00       ( k2_xboole_0 @
% 0.81/1.00         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 0.81/1.00  thf('8', plain,
% 0.81/1.00      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.81/1.00         ((k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.81/1.00           = (k2_xboole_0 @ (k3_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34) @ 
% 0.81/1.00              (k2_tarski @ X35 @ X36)))),
% 0.81/1.00      inference('cnf', [status(esa)], [t60_enumset1])).
% 0.81/1.00  thf('9', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.81/1.00         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 0.81/1.00           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.81/1.00              (k2_tarski @ X5 @ X4)))),
% 0.81/1.00      inference('sup+', [status(thm)], ['7', '8'])).
% 0.81/1.00  thf('10', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.00         ((k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.81/1.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.81/1.00      inference('sup+', [status(thm)], ['6', '9'])).
% 0.81/1.00  thf(t74_enumset1, axiom,
% 0.81/1.00    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.81/1.00     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.81/1.00       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.81/1.00  thf('11', plain,
% 0.81/1.00      (![X75 : $i, X76 : $i, X77 : $i, X78 : $i, X79 : $i, X80 : $i]:
% 0.81/1.00         ((k5_enumset1 @ X75 @ X75 @ X76 @ X77 @ X78 @ X79 @ X80)
% 0.81/1.00           = (k4_enumset1 @ X75 @ X76 @ X77 @ X78 @ X79 @ X80))),
% 0.81/1.00      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.81/1.00  thf(t73_enumset1, axiom,
% 0.81/1.00    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.81/1.00     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.81/1.00       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.81/1.00  thf('12', plain,
% 0.81/1.00      (![X70 : $i, X71 : $i, X72 : $i, X73 : $i, X74 : $i]:
% 0.81/1.00         ((k4_enumset1 @ X70 @ X70 @ X71 @ X72 @ X73 @ X74)
% 0.81/1.00           = (k3_enumset1 @ X70 @ X71 @ X72 @ X73 @ X74))),
% 0.81/1.00      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.81/1.00  thf('13', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.81/1.00         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.81/1.00           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.81/1.00      inference('sup+', [status(thm)], ['11', '12'])).
% 0.81/1.00  thf('14', plain,
% 0.81/1.00      (![X66 : $i, X67 : $i, X68 : $i, X69 : $i]:
% 0.81/1.00         ((k3_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69)
% 0.81/1.00           = (k2_enumset1 @ X66 @ X67 @ X68 @ X69))),
% 0.81/1.00      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.81/1.00  thf('15', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.00         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 0.81/1.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.81/1.00      inference('demod', [status(thm)], ['10', '13', '14'])).
% 0.81/1.00  thf('16', plain,
% 0.81/1.00      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.81/1.00         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.81/1.00      inference('demod', [status(thm)], ['3', '15'])).
% 0.81/1.00  thf('17', plain,
% 0.81/1.00      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.81/1.00         ((k1_enumset1 @ X8 @ X6 @ X7) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.81/1.00      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.81/1.00  thf('18', plain,
% 0.81/1.00      (![X61 : $i, X62 : $i]:
% 0.81/1.00         ((k1_enumset1 @ X61 @ X61 @ X62) = (k2_tarski @ X61 @ X62))),
% 0.81/1.00      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.81/1.00  thf('19', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i]:
% 0.81/1.00         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.81/1.00      inference('sup+', [status(thm)], ['17', '18'])).
% 0.81/1.00  thf(t102_enumset1, axiom,
% 0.81/1.00    (![A:$i,B:$i,C:$i]:
% 0.81/1.00     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.81/1.00  thf('20', plain,
% 0.81/1.00      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.81/1.00         ((k1_enumset1 @ X11 @ X10 @ X9) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.81/1.00      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.81/1.00  thf('21', plain,
% 0.81/1.00      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.81/1.00         ((k1_enumset1 @ X8 @ X6 @ X7) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.81/1.00      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.81/1.00  thf('22', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.00         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.81/1.00      inference('sup+', [status(thm)], ['20', '21'])).
% 0.81/1.00  thf('23', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i]:
% 0.81/1.00         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.81/1.00      inference('sup+', [status(thm)], ['4', '5'])).
% 0.81/1.00  thf(t69_enumset1, axiom,
% 0.81/1.00    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.81/1.00  thf('24', plain,
% 0.81/1.00      (![X60 : $i]: ((k2_tarski @ X60 @ X60) = (k1_tarski @ X60))),
% 0.81/1.00      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.81/1.00  thf('25', plain,
% 0.81/1.00      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.81/1.00      inference('sup+', [status(thm)], ['23', '24'])).
% 0.81/1.00  thf('26', plain,
% 0.81/1.00      (![X66 : $i, X67 : $i, X68 : $i, X69 : $i]:
% 0.81/1.00         ((k3_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69)
% 0.81/1.00           = (k2_enumset1 @ X66 @ X67 @ X68 @ X69))),
% 0.81/1.00      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.81/1.00  thf(t66_enumset1, axiom,
% 0.81/1.00    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.81/1.00     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.81/1.00       ( k2_xboole_0 @
% 0.81/1.00         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 0.81/1.00  thf('27', plain,
% 0.81/1.00      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, 
% 0.81/1.00         X51 : $i]:
% 0.81/1.00         ((k6_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51)
% 0.81/1.00           = (k2_xboole_0 @ (k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48) @ 
% 0.81/1.00              (k1_enumset1 @ X49 @ X50 @ X51)))),
% 0.81/1.00      inference('cnf', [status(esa)], [t66_enumset1])).
% 0.81/1.00  thf('28', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.81/1.00         ((k6_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4)
% 0.81/1.00           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.81/1.00              (k1_enumset1 @ X6 @ X5 @ X4)))),
% 0.81/1.00      inference('sup+', [status(thm)], ['26', '27'])).
% 0.81/1.00  thf(t75_enumset1, axiom,
% 0.81/1.00    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.81/1.00     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.81/1.00       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.81/1.00  thf('29', plain,
% 0.81/1.00      (![X81 : $i, X82 : $i, X83 : $i, X84 : $i, X85 : $i, X86 : $i, X87 : $i]:
% 0.81/1.00         ((k6_enumset1 @ X81 @ X81 @ X82 @ X83 @ X84 @ X85 @ X86 @ X87)
% 0.81/1.00           = (k5_enumset1 @ X81 @ X82 @ X83 @ X84 @ X85 @ X86 @ X87))),
% 0.81/1.00      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.81/1.00  thf('30', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.81/1.00         ((k5_enumset1 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4)
% 0.81/1.00           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.81/1.00              (k1_enumset1 @ X6 @ X5 @ X4)))),
% 0.81/1.00      inference('demod', [status(thm)], ['28', '29'])).
% 0.81/1.00  thf('31', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.00         ((k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.81/1.00           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.81/1.00      inference('sup+', [status(thm)], ['25', '30'])).
% 0.81/1.00  thf('32', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.81/1.00         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.81/1.00           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.81/1.00      inference('sup+', [status(thm)], ['11', '12'])).
% 0.81/1.00  thf('33', plain,
% 0.81/1.00      (![X66 : $i, X67 : $i, X68 : $i, X69 : $i]:
% 0.81/1.00         ((k3_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69)
% 0.81/1.00           = (k2_enumset1 @ X66 @ X67 @ X68 @ X69))),
% 0.81/1.00      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.81/1.00  thf('34', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.00         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 0.81/1.00           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.81/1.00      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.81/1.00  thf('35', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.00         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0)
% 0.81/1.00           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.81/1.00      inference('sup+', [status(thm)], ['22', '34'])).
% 0.81/1.00  thf('36', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.00         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1)
% 0.81/1.00           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.81/1.00      inference('sup+', [status(thm)], ['19', '35'])).
% 0.81/1.00  thf('37', plain,
% 0.81/1.00      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.81/1.00      inference('sup+', [status(thm)], ['23', '24'])).
% 0.81/1.00  thf('38', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.81/1.00         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 0.81/1.00           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.81/1.00              (k2_tarski @ X5 @ X4)))),
% 0.81/1.00      inference('sup+', [status(thm)], ['7', '8'])).
% 0.81/1.00  thf('39', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.00         ((k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X2 @ X1)
% 0.81/1.00           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.81/1.00      inference('sup+', [status(thm)], ['37', '38'])).
% 0.81/1.00  thf('40', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.81/1.00         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.81/1.00           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.81/1.00      inference('sup+', [status(thm)], ['11', '12'])).
% 0.81/1.00  thf('41', plain,
% 0.81/1.00      (![X66 : $i, X67 : $i, X68 : $i, X69 : $i]:
% 0.81/1.00         ((k3_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69)
% 0.81/1.00           = (k2_enumset1 @ X66 @ X67 @ X68 @ X69))),
% 0.81/1.00      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.81/1.00  thf('42', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.00         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.81/1.00           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.81/1.00      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.81/1.00  thf('43', plain,
% 0.81/1.00      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.81/1.00         ((k2_enumset1 @ X63 @ X63 @ X64 @ X65)
% 0.81/1.00           = (k1_enumset1 @ X63 @ X64 @ X65))),
% 0.81/1.00      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.81/1.00  thf('44', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.00         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 0.81/1.00           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.81/1.00      inference('sup+', [status(thm)], ['42', '43'])).
% 0.81/1.00  thf('45', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.00         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.81/1.00      inference('demod', [status(thm)], ['36', '44'])).
% 0.81/1.00  thf(t98_enumset1, axiom,
% 0.81/1.00    (![A:$i,B:$i,C:$i]:
% 0.81/1.00     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.81/1.00  thf('46', plain,
% 0.81/1.00      (![X88 : $i, X89 : $i, X90 : $i]:
% 0.81/1.00         ((k1_enumset1 @ X88 @ X90 @ X89) = (k1_enumset1 @ X88 @ X89 @ X90))),
% 0.81/1.00      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.81/1.00  thf('47', plain,
% 0.81/1.00      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 0.81/1.00         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.81/1.00      inference('demod', [status(thm)], ['16', '45', '46'])).
% 0.81/1.00  thf('48', plain, ($false), inference('simplify', [status(thm)], ['47'])).
% 0.81/1.00  
% 0.81/1.00  % SZS output end Refutation
% 0.81/1.00  
% 0.81/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
