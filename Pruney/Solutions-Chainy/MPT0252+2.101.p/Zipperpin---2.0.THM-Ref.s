%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sELVcCXapD

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:29 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 241 expanded)
%              Number of leaves         :   36 (  94 expanded)
%              Depth                    :   22
%              Number of atoms          : 1493 (3152 expanded)
%              Number of equality atoms :  102 ( 212 expanded)
%              Maximal formula depth    :   25 (  12 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

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

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_enumset1 @ X49 @ X49 @ X50 )
      = ( k2_tarski @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_enumset1 @ X30 @ X29 @ X28 @ X27 )
      = ( k2_enumset1 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( k2_enumset1 @ X51 @ X51 @ X52 @ X53 )
      = ( k1_enumset1 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('7',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( k2_enumset1 @ X51 @ X51 @ X52 @ X53 )
      = ( k1_enumset1 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('9',plain,(
    ! [X69: $i,X70: $i,X71: $i,X72: $i,X73: $i,X74: $i,X75: $i] :
      ( ( k6_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 @ X75 )
      = ( k5_enumset1 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('10',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ( k5_enumset1 @ X63 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68 )
      = ( k4_enumset1 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('12',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62 )
      = ( k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('15',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57 )
      = ( k2_enumset1 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ( k5_enumset1 @ X63 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68 )
      = ( k4_enumset1 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('19',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k6_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 ) @ ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 @ X2 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62 )
      = ( k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('23',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57 )
      = ( k2_enumset1 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('24',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( k2_enumset1 @ X51 @ X51 @ X52 @ X53 )
      = ( k1_enumset1 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['21','22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('29',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57 )
      = ( k2_enumset1 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62 )
      = ( k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57 )
      = ( k2_enumset1 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62 )
      = ( k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X0 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62 )
      = ( k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('48',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57 )
      = ( k2_enumset1 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('49',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_enumset1 @ X30 @ X29 @ X28 @ X27 )
      = ( k2_enumset1 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62 )
      = ( k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['44','45','55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_enumset1 @ X3 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ( k5_enumset1 @ X63 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68 )
      = ( k4_enumset1 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('63',plain,(
    ! [X48: $i] :
      ( ( k2_tarski @ X48 @ X48 )
      = ( k1_tarski @ X48 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('64',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ( k5_enumset1 @ X63 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68 )
      = ( k4_enumset1 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t133_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k2_tarski @ H @ I ) ) ) )).

thf('65',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k7_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) @ ( k2_tarski @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t133_enumset1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X7 @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(d7_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i,J: $i] :
      ( ( J
        = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) )
    <=> ! [K: $i] :
          ( ( r2_hidden @ K @ J )
        <=> ~ ( ( K != I )
              & ( K != H )
              & ( K != G )
              & ( K != F )
              & ( K != E )
              & ( K != D )
              & ( K != C )
              & ( K != B )
              & ( K != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [K: $i,I: $i,H: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( K != A )
        & ( K != B )
        & ( K != C )
        & ( K != D )
        & ( K != E )
        & ( K != F )
        & ( K != G )
        & ( K != H )
        & ( K != I ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i,J: $i] :
      ( ( J
        = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) )
    <=> ! [K: $i] :
          ( ( r2_hidden @ K @ J )
        <=> ~ ( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      | ( r2_hidden @ X14 @ X24 )
      | ( X24
       != ( k7_enumset1 @ X23 @ X22 @ X21 @ X20 @ X19 @ X18 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('68',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X14 @ ( k7_enumset1 @ X23 @ X22 @ X21 @ X20 @ X19 @ X18 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ ( k2_xboole_0 @ ( k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X7 ) ) ),
    inference('sup+',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X4 != X3 )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('71',plain,(
    ! [X3: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X3 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X3 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X6 @ ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('75',plain,(
    ! [X69: $i,X70: $i,X71: $i,X72: $i,X73: $i,X74: $i,X75: $i] :
      ( ( k6_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 @ X75 )
      = ( k5_enumset1 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X6 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','80'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('82',plain,(
    ! [X76: $i,X77: $i] :
      ( ( r1_tarski @ X76 @ ( k3_tarski @ X77 ) )
      | ~ ( r2_hidden @ X76 @ X77 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('84',plain,(
    ! [X78: $i,X79: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X78 @ X79 ) )
      = ( k2_xboole_0 @ X78 @ X79 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['1','87'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('89',plain,(
    ! [X80: $i,X81: $i,X82: $i] :
      ( ( r2_hidden @ X80 @ X81 )
      | ~ ( r1_tarski @ ( k2_tarski @ X80 @ X82 ) @ X81 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('90',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['0','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sELVcCXapD
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.14  % Solved by: fo/fo7.sh
% 0.91/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.14  % done 1255 iterations in 0.686s
% 0.91/1.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.14  % SZS output start Refutation
% 0.91/1.14  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.91/1.14                                               $i > $i > $i > $i > $o).
% 0.91/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.14  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.91/1.14  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.14  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.91/1.14  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.91/1.14  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.91/1.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.14  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.91/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.14  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.91/1.14                                           $i > $i > $i).
% 0.91/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.14  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.91/1.14                                           $i > $i).
% 0.91/1.14  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.91/1.14  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.91/1.14  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.91/1.14  thf(t47_zfmisc_1, conjecture,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.91/1.14       ( r2_hidden @ A @ C ) ))).
% 0.91/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.14    (~( ![A:$i,B:$i,C:$i]:
% 0.91/1.14        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.91/1.14          ( r2_hidden @ A @ C ) ) )),
% 0.91/1.14    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.91/1.14  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('1', plain,
% 0.91/1.14      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(t70_enumset1, axiom,
% 0.91/1.14    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.91/1.14  thf('2', plain,
% 0.91/1.14      (![X49 : $i, X50 : $i]:
% 0.91/1.14         ((k1_enumset1 @ X49 @ X49 @ X50) = (k2_tarski @ X49 @ X50))),
% 0.91/1.14      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.91/1.14  thf(t125_enumset1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.14     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.91/1.14  thf('3', plain,
% 0.91/1.14      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X30 @ X29 @ X28 @ X27)
% 0.91/1.14           = (k2_enumset1 @ X27 @ X28 @ X29 @ X30))),
% 0.91/1.14      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.91/1.14  thf(t71_enumset1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.91/1.14  thf('4', plain,
% 0.91/1.14      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X51 @ X51 @ X52 @ X53)
% 0.91/1.14           = (k1_enumset1 @ X51 @ X52 @ X53))),
% 0.91/1.14      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.91/1.14  thf('5', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.91/1.14      inference('sup+', [status(thm)], ['3', '4'])).
% 0.91/1.14  thf('6', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.91/1.14      inference('sup+', [status(thm)], ['3', '4'])).
% 0.91/1.14  thf('7', plain,
% 0.91/1.14      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X51 @ X51 @ X52 @ X53)
% 0.91/1.14           = (k1_enumset1 @ X51 @ X52 @ X53))),
% 0.91/1.14      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.91/1.14  thf('8', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 0.91/1.14      inference('sup+', [status(thm)], ['6', '7'])).
% 0.91/1.14  thf(t75_enumset1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.91/1.14     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.91/1.14       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.91/1.14  thf('9', plain,
% 0.91/1.14      (![X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i, X74 : $i, X75 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 @ X75)
% 0.91/1.14           = (k5_enumset1 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 @ X75))),
% 0.91/1.14      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.91/1.14  thf(t74_enumset1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.91/1.14     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.91/1.14       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.91/1.14  thf('10', plain,
% 0.91/1.14      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 0.91/1.14         ((k5_enumset1 @ X63 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68)
% 0.91/1.14           = (k4_enumset1 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68))),
% 0.91/1.14      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.91/1.14  thf('11', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.91/1.14           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['9', '10'])).
% 0.91/1.14  thf(t73_enumset1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.91/1.14     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.91/1.14       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.91/1.14  thf('12', plain,
% 0.91/1.14      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 0.91/1.14         ((k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62)
% 0.91/1.14           = (k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62))),
% 0.91/1.14      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.91/1.14  thf('13', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.91/1.14           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['11', '12'])).
% 0.91/1.14  thf('14', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.91/1.14      inference('sup+', [status(thm)], ['3', '4'])).
% 0.91/1.14  thf(t72_enumset1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.14     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.91/1.14  thf('15', plain,
% 0.91/1.14      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.91/1.14         ((k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57)
% 0.91/1.14           = (k2_enumset1 @ X54 @ X55 @ X56 @ X57))),
% 0.91/1.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.91/1.14  thf('16', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['14', '15'])).
% 0.91/1.14  thf('17', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 @ X0)
% 0.91/1.14           = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.91/1.14      inference('sup+', [status(thm)], ['13', '16'])).
% 0.91/1.14  thf('18', plain,
% 0.91/1.14      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 0.91/1.14         ((k5_enumset1 @ X63 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68)
% 0.91/1.14           = (k4_enumset1 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68))),
% 0.91/1.14      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.91/1.14  thf(t68_enumset1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.91/1.14     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.91/1.14       ( k2_xboole_0 @
% 0.91/1.14         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.91/1.14  thf('19', plain,
% 0.91/1.14      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, 
% 0.91/1.14         X47 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47)
% 0.91/1.14           = (k2_xboole_0 @ 
% 0.91/1.14              (k5_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46) @ 
% 0.91/1.14              (k1_tarski @ X47)))),
% 0.91/1.14      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.91/1.14  thf('20', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.91/1.14           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.91/1.14              (k1_tarski @ X6)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['18', '19'])).
% 0.91/1.14  thf('21', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.91/1.14           = (k2_xboole_0 @ (k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 @ X2) @ 
% 0.91/1.14              (k1_tarski @ X2)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['17', '20'])).
% 0.91/1.14  thf('22', plain,
% 0.91/1.14      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 0.91/1.14         ((k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62)
% 0.91/1.14           = (k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62))),
% 0.91/1.14      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.91/1.14  thf('23', plain,
% 0.91/1.14      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.91/1.14         ((k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57)
% 0.91/1.14           = (k2_enumset1 @ X54 @ X55 @ X56 @ X57))),
% 0.91/1.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.91/1.14  thf('24', plain,
% 0.91/1.14      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X51 @ X51 @ X52 @ X53)
% 0.91/1.14           = (k1_enumset1 @ X51 @ X52 @ X53))),
% 0.91/1.14      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.91/1.14  thf('25', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['23', '24'])).
% 0.91/1.14  thf('26', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.91/1.14           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X1 @ X2) @ (k1_tarski @ X2)))),
% 0.91/1.14      inference('demod', [status(thm)], ['21', '22', '25'])).
% 0.91/1.14  thf('27', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k1_enumset1 @ X1 @ X1 @ X0)
% 0.91/1.14           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['8', '26'])).
% 0.91/1.14  thf('28', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.91/1.14           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['11', '12'])).
% 0.91/1.14  thf('29', plain,
% 0.91/1.14      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.91/1.14         ((k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57)
% 0.91/1.14           = (k2_enumset1 @ X54 @ X55 @ X56 @ X57))),
% 0.91/1.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.91/1.14  thf('30', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.91/1.14           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['28', '29'])).
% 0.91/1.14  thf('31', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.91/1.14           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.91/1.14              (k1_tarski @ X6)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['18', '19'])).
% 0.91/1.14  thf('32', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.91/1.14           = (k2_xboole_0 @ (k4_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1) @ 
% 0.91/1.14              (k1_tarski @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['30', '31'])).
% 0.91/1.14  thf('33', plain,
% 0.91/1.14      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 0.91/1.14         ((k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62)
% 0.91/1.14           = (k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62))),
% 0.91/1.14      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.91/1.14  thf('34', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['23', '24'])).
% 0.91/1.14  thf('35', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.91/1.14           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.91/1.14  thf('36', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k1_enumset1 @ X1 @ X1 @ X0) = (k2_enumset1 @ X1 @ X0 @ X0 @ X1))),
% 0.91/1.14      inference('demod', [status(thm)], ['27', '35'])).
% 0.91/1.14  thf('37', plain,
% 0.91/1.14      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.91/1.14         ((k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57)
% 0.91/1.14           = (k2_enumset1 @ X54 @ X55 @ X56 @ X57))),
% 0.91/1.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.91/1.14  thf('38', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k3_enumset1 @ X1 @ X1 @ X0 @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('39', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.91/1.14           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['9', '10'])).
% 0.91/1.14  thf('40', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.91/1.14           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.91/1.14              (k1_tarski @ X6)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['18', '19'])).
% 0.91/1.14  thf('41', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.91/1.14         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.91/1.14           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.91/1.14              (k1_tarski @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['39', '40'])).
% 0.91/1.14  thf('42', plain,
% 0.91/1.14      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 0.91/1.14         ((k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62)
% 0.91/1.14           = (k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62))),
% 0.91/1.14      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.91/1.14  thf('43', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.91/1.14         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.91/1.14           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.91/1.14              (k1_tarski @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['41', '42'])).
% 0.91/1.14  thf('44', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k4_enumset1 @ X1 @ X1 @ X0 @ X0 @ X1 @ X2)
% 0.91/1.14           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['38', '43'])).
% 0.91/1.14  thf('45', plain,
% 0.91/1.14      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 0.91/1.14         ((k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62)
% 0.91/1.14           = (k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62))),
% 0.91/1.14      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.91/1.14  thf('46', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.91/1.14           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.91/1.14              (k1_tarski @ X6)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['18', '19'])).
% 0.91/1.14  thf('47', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.91/1.14           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['11', '12'])).
% 0.91/1.14  thf('48', plain,
% 0.91/1.14      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.91/1.14         ((k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57)
% 0.91/1.14           = (k2_enumset1 @ X54 @ X55 @ X56 @ X57))),
% 0.91/1.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.91/1.14  thf('49', plain,
% 0.91/1.14      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X30 @ X29 @ X28 @ X27)
% 0.91/1.14           = (k2_enumset1 @ X27 @ X28 @ X29 @ X30))),
% 0.91/1.14      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.91/1.14  thf('50', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 0.91/1.14           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['48', '49'])).
% 0.91/1.14  thf('51', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 0.91/1.14           = (k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['47', '50'])).
% 0.91/1.14  thf('52', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 0.91/1.14           = (k2_xboole_0 @ (k4_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1) @ 
% 0.91/1.14              (k1_tarski @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['46', '51'])).
% 0.91/1.14  thf('53', plain,
% 0.91/1.14      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 0.91/1.14         ((k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62)
% 0.91/1.14           = (k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62))),
% 0.91/1.14      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.91/1.14  thf('54', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['23', '24'])).
% 0.91/1.14  thf('55', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 0.91/1.14           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.91/1.14  thf('56', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.91/1.14      inference('sup+', [status(thm)], ['3', '4'])).
% 0.91/1.14  thf('57', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((k3_enumset1 @ X1 @ X0 @ X0 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.91/1.14      inference('demod', [status(thm)], ['44', '45', '55', '56'])).
% 0.91/1.14  thf('58', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.91/1.14         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.91/1.14           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.91/1.14              (k1_tarski @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['41', '42'])).
% 0.91/1.14  thf('59', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k4_enumset1 @ X2 @ X1 @ X1 @ X2 @ X0 @ X3)
% 0.91/1.14           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['57', '58'])).
% 0.91/1.14  thf('60', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 0.91/1.14           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.91/1.14      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.91/1.14  thf('61', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((k4_enumset1 @ X2 @ X1 @ X1 @ X2 @ X0 @ X3)
% 0.91/1.14           = (k2_enumset1 @ X3 @ X0 @ X1 @ X2))),
% 0.91/1.14      inference('demod', [status(thm)], ['59', '60'])).
% 0.91/1.14  thf('62', plain,
% 0.91/1.14      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 0.91/1.14         ((k5_enumset1 @ X63 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68)
% 0.91/1.14           = (k4_enumset1 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68))),
% 0.91/1.14      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.91/1.14  thf(t69_enumset1, axiom,
% 0.91/1.14    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.91/1.14  thf('63', plain,
% 0.91/1.14      (![X48 : $i]: ((k2_tarski @ X48 @ X48) = (k1_tarski @ X48))),
% 0.91/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.91/1.14  thf('64', plain,
% 0.91/1.14      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 0.91/1.14         ((k5_enumset1 @ X63 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68)
% 0.91/1.14           = (k4_enumset1 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68))),
% 0.91/1.14      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.91/1.14  thf(t133_enumset1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.91/1.14     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.91/1.14       ( k2_xboole_0 @
% 0.91/1.14         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k2_tarski @ H @ I ) ) ))).
% 0.91/1.14  thf('65', plain,
% 0.91/1.14      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, 
% 0.91/1.14         X38 : $i, X39 : $i]:
% 0.91/1.14         ((k7_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)
% 0.91/1.14           = (k2_xboole_0 @ 
% 0.91/1.14              (k5_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37) @ 
% 0.91/1.14              (k2_tarski @ X38 @ X39)))),
% 0.91/1.14      inference('cnf', [status(esa)], [t133_enumset1])).
% 0.91/1.14  thf('66', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.14         ((k7_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6)
% 0.91/1.14           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.91/1.14              (k2_tarski @ X7 @ X6)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['64', '65'])).
% 0.91/1.14  thf(d7_enumset1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i,J:$i]:
% 0.91/1.14     ( ( ( J ) = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) ) <=>
% 0.91/1.14       ( ![K:$i]:
% 0.91/1.14         ( ( r2_hidden @ K @ J ) <=>
% 0.91/1.14           ( ~( ( ( K ) != ( I ) ) & ( ( K ) != ( H ) ) & ( ( K ) != ( G ) ) & 
% 0.91/1.14                ( ( K ) != ( F ) ) & ( ( K ) != ( E ) ) & ( ( K ) != ( D ) ) & 
% 0.91/1.14                ( ( K ) != ( C ) ) & ( ( K ) != ( B ) ) & ( ( K ) != ( A ) ) ) ) ) ) ))).
% 0.91/1.14  thf(zf_stmt_1, type, zip_tseitin_0 :
% 0.91/1.14      $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.91/1.14  thf(zf_stmt_2, axiom,
% 0.91/1.14    (![K:$i,I:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.91/1.14     ( ( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.91/1.14       ( ( ( K ) != ( A ) ) & ( ( K ) != ( B ) ) & ( ( K ) != ( C ) ) & 
% 0.91/1.14         ( ( K ) != ( D ) ) & ( ( K ) != ( E ) ) & ( ( K ) != ( F ) ) & 
% 0.91/1.14         ( ( K ) != ( G ) ) & ( ( K ) != ( H ) ) & ( ( K ) != ( I ) ) ) ))).
% 0.91/1.14  thf(zf_stmt_3, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i,J:$i]:
% 0.91/1.14     ( ( ( J ) = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) ) <=>
% 0.91/1.14       ( ![K:$i]:
% 0.91/1.14         ( ( r2_hidden @ K @ J ) <=>
% 0.91/1.14           ( ~( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.91/1.14  thf('67', plain,
% 0.91/1.14      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 0.91/1.14         X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.91/1.14         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ 
% 0.91/1.14           X22 @ X23)
% 0.91/1.14          | (r2_hidden @ X14 @ X24)
% 0.91/1.14          | ((X24)
% 0.91/1.14              != (k7_enumset1 @ X23 @ X22 @ X21 @ X20 @ X19 @ X18 @ X17 @ 
% 0.91/1.14                  X16 @ X15)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.14  thf('68', plain,
% 0.91/1.14      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 0.91/1.14         X21 : $i, X22 : $i, X23 : $i]:
% 0.91/1.14         ((r2_hidden @ X14 @ 
% 0.91/1.14           (k7_enumset1 @ X23 @ X22 @ X21 @ X20 @ X19 @ X18 @ X17 @ X16 @ X15))
% 0.91/1.14          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ 
% 0.91/1.14             X22 @ X23))),
% 0.91/1.14      inference('simplify', [status(thm)], ['67'])).
% 0.91/1.14  thf('69', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.91/1.14         X7 : $i, X8 : $i]:
% 0.91/1.14         ((r2_hidden @ X8 @ 
% 0.91/1.14           (k2_xboole_0 @ (k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.91/1.14            (k2_tarski @ X1 @ X0)))
% 0.91/1.14          | (zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X7))),
% 0.91/1.14      inference('sup+', [status(thm)], ['66', '68'])).
% 0.91/1.14  thf('70', plain,
% 0.91/1.14      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, 
% 0.91/1.14         X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.14         (((X4) != (X3))
% 0.91/1.14          | ~ (zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ 
% 0.91/1.14               X3))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.91/1.14  thf('71', plain,
% 0.91/1.14      (![X3 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, 
% 0.91/1.14         X11 : $i, X12 : $i]:
% 0.91/1.14         ~ (zip_tseitin_0 @ X3 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X3)),
% 0.91/1.14      inference('simplify', [status(thm)], ['70'])).
% 0.91/1.14  thf('72', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.14         (r2_hidden @ X0 @ 
% 0.91/1.14          (k2_xboole_0 @ (k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5) @ 
% 0.91/1.14           (k2_tarski @ X6 @ X7)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['69', '71'])).
% 0.91/1.14  thf('73', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.14         (r2_hidden @ X6 @ 
% 0.91/1.14          (k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.91/1.14           (k1_tarski @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['63', '72'])).
% 0.91/1.14  thf('74', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.91/1.14           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.91/1.14              (k1_tarski @ X6)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['18', '19'])).
% 0.91/1.14  thf('75', plain,
% 0.91/1.14      (![X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i, X74 : $i, X75 : $i]:
% 0.91/1.14         ((k6_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 @ X75)
% 0.91/1.14           = (k5_enumset1 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 @ X75))),
% 0.91/1.14      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.91/1.14  thf('76', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.14         ((k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.91/1.14           (k1_tarski @ X0)) = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['74', '75'])).
% 0.91/1.14  thf('77', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.14         (r2_hidden @ X6 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['73', '76'])).
% 0.91/1.14  thf('78', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.91/1.14         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['62', '77'])).
% 0.91/1.14  thf('79', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         (r2_hidden @ X0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['61', '78'])).
% 0.91/1.14  thf('80', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['5', '79'])).
% 0.91/1.14  thf('81', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['2', '80'])).
% 0.91/1.14  thf(l49_zfmisc_1, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.91/1.14  thf('82', plain,
% 0.91/1.14      (![X76 : $i, X77 : $i]:
% 0.91/1.14         ((r1_tarski @ X76 @ (k3_tarski @ X77)) | ~ (r2_hidden @ X76 @ X77))),
% 0.91/1.14      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.91/1.14  thf('83', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (r1_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['81', '82'])).
% 0.91/1.14  thf(l51_zfmisc_1, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.14  thf('84', plain,
% 0.91/1.14      (![X78 : $i, X79 : $i]:
% 0.91/1.14         ((k3_tarski @ (k2_tarski @ X78 @ X79)) = (k2_xboole_0 @ X78 @ X79))),
% 0.91/1.14      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.91/1.14  thf('85', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['83', '84'])).
% 0.91/1.14  thf(t1_xboole_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.91/1.14       ( r1_tarski @ A @ C ) ))).
% 0.91/1.14  thf('86', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (~ (r1_tarski @ X0 @ X1)
% 0.91/1.14          | ~ (r1_tarski @ X1 @ X2)
% 0.91/1.14          | (r1_tarski @ X0 @ X2))),
% 0.91/1.14      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.91/1.14  thf('87', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.91/1.14      inference('sup-', [status(thm)], ['85', '86'])).
% 0.91/1.14  thf('88', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.91/1.14      inference('sup-', [status(thm)], ['1', '87'])).
% 0.91/1.14  thf(t38_zfmisc_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.91/1.14       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.91/1.14  thf('89', plain,
% 0.91/1.14      (![X80 : $i, X81 : $i, X82 : $i]:
% 0.91/1.14         ((r2_hidden @ X80 @ X81)
% 0.91/1.14          | ~ (r1_tarski @ (k2_tarski @ X80 @ X82) @ X81))),
% 0.91/1.14      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.91/1.14  thf('90', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.91/1.14      inference('sup-', [status(thm)], ['88', '89'])).
% 0.91/1.14  thf('91', plain, ($false), inference('demod', [status(thm)], ['0', '90'])).
% 0.91/1.14  
% 0.91/1.14  % SZS output end Refutation
% 0.91/1.14  
% 0.99/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
