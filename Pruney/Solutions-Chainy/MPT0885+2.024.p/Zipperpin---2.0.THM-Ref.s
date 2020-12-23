%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eQoL81UepD

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:30 EST 2020

% Result     : Theorem 6.02s
% Output     : Refutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :   71 (  96 expanded)
%              Number of leaves         :   30 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  848 (1215 expanded)
%              Number of equality atoms :   53 (  78 expanded)
%              Maximal formula depth    :   19 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(t45_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) )
        = ( k2_enumset1 @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_E ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('4',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( k1_enumset1 @ X47 @ X49 @ X48 )
      = ( k1_enumset1 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X0 @ X1 )
      = ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k5_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 )
      = ( k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k6_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('11',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k6_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      = ( k5_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('12',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k5_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 )
      = ( k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('15',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k4_enumset1 @ X2 @ X2 @ X2 @ X0 @ X1 @ X3 ) ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('19',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('20',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k3_enumset1 @ X2 @ X2 @ X0 @ X1 @ X3 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_E ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','25'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('27',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( k3_mcart_1 @ X60 @ X61 @ X62 )
      = ( k4_tarski @ ( k4_tarski @ X60 @ X61 ) @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('28',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( k3_mcart_1 @ X60 @ X61 @ X62 )
      = ( k4_tarski @ ( k4_tarski @ X60 @ X61 ) @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('29',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X52 @ X55 ) @ ( k2_tarski @ X53 @ X54 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X52 @ X53 ) @ ( k4_tarski @ X52 @ X54 ) @ ( k4_tarski @ X55 @ X53 ) @ ( k4_tarski @ X55 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( k3_mcart_1 @ X60 @ X61 @ X62 )
      = ( k4_tarski @ ( k4_tarski @ X60 @ X61 ) @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( k3_mcart_1 @ X60 @ X61 @ X62 )
      = ( k4_tarski @ ( k4_tarski @ X60 @ X61 ) @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('36',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X56 ) @ ( k2_tarski @ X57 @ X58 ) )
      = ( k2_tarski @ ( k4_tarski @ X56 @ X57 ) @ ( k4_tarski @ X56 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('37',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k3_zfmisc_1 @ X63 @ X64 @ X65 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X64 ) @ X65 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('38',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['26','35','36','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eQoL81UepD
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:45:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 6.02/6.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.02/6.20  % Solved by: fo/fo7.sh
% 6.02/6.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.02/6.20  % done 4875 iterations in 5.744s
% 6.02/6.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.02/6.20  % SZS output start Refutation
% 6.02/6.20  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.02/6.20  thf(sk_A_type, type, sk_A: $i).
% 6.02/6.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.02/6.20  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.02/6.20  thf(sk_B_type, type, sk_B: $i).
% 6.02/6.20  thf(sk_E_type, type, sk_E: $i).
% 6.02/6.20  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 6.02/6.20  thf(sk_C_type, type, sk_C: $i).
% 6.02/6.20  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 6.02/6.20  thf(sk_D_type, type, sk_D: $i).
% 6.02/6.20  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 6.02/6.20  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 6.02/6.20  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.02/6.20  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 6.02/6.20  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 6.02/6.20  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 6.02/6.20  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 6.02/6.20  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 6.02/6.20                                           $i > $i).
% 6.02/6.20  thf(t45_mcart_1, conjecture,
% 6.02/6.20    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.02/6.20     ( ( k3_zfmisc_1 @
% 6.02/6.20         ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) =
% 6.02/6.20       ( k2_enumset1 @
% 6.02/6.20         ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ 
% 6.02/6.20         ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ))).
% 6.02/6.20  thf(zf_stmt_0, negated_conjecture,
% 6.02/6.20    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.02/6.20        ( ( k3_zfmisc_1 @
% 6.02/6.20            ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) =
% 6.02/6.20          ( k2_enumset1 @
% 6.02/6.20            ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ 
% 6.02/6.20            ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) )),
% 6.02/6.20    inference('cnf.neg', [status(esa)], [t45_mcart_1])).
% 6.02/6.20  thf('0', plain,
% 6.02/6.20      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 6.02/6.20         (k2_tarski @ sk_D @ sk_E))
% 6.02/6.20         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_D) @ 
% 6.02/6.20             (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 6.02/6.20             (k3_mcart_1 @ sk_A @ sk_B @ sk_E) @ 
% 6.02/6.20             (k3_mcart_1 @ sk_A @ sk_C @ sk_E)))),
% 6.02/6.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.20  thf(t72_enumset1, axiom,
% 6.02/6.20    (![A:$i,B:$i,C:$i,D:$i]:
% 6.02/6.20     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 6.02/6.20  thf('1', plain,
% 6.02/6.20      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 6.02/6.20         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 6.02/6.20           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 6.02/6.20      inference('cnf', [status(esa)], [t72_enumset1])).
% 6.02/6.20  thf(t71_enumset1, axiom,
% 6.02/6.20    (![A:$i,B:$i,C:$i]:
% 6.02/6.20     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 6.02/6.20  thf('2', plain,
% 6.02/6.20      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.02/6.20         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 6.02/6.20           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 6.02/6.20      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.02/6.20  thf('3', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.02/6.20         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.02/6.20      inference('sup+', [status(thm)], ['1', '2'])).
% 6.02/6.20  thf(t98_enumset1, axiom,
% 6.02/6.20    (![A:$i,B:$i,C:$i]:
% 6.02/6.20     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 6.02/6.20  thf('4', plain,
% 6.02/6.20      (![X47 : $i, X48 : $i, X49 : $i]:
% 6.02/6.20         ((k1_enumset1 @ X47 @ X49 @ X48) = (k1_enumset1 @ X47 @ X48 @ X49))),
% 6.02/6.20      inference('cnf', [status(esa)], [t98_enumset1])).
% 6.02/6.20  thf('5', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.02/6.20         ((k1_enumset1 @ X2 @ X0 @ X1) = (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0))),
% 6.02/6.20      inference('sup+', [status(thm)], ['3', '4'])).
% 6.02/6.20  thf('6', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.02/6.20         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.02/6.20      inference('sup+', [status(thm)], ['1', '2'])).
% 6.02/6.20  thf('7', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.02/6.20         ((k3_enumset1 @ X2 @ X2 @ X2 @ X0 @ X1)
% 6.02/6.20           = (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0))),
% 6.02/6.20      inference('sup+', [status(thm)], ['5', '6'])).
% 6.02/6.20  thf(t74_enumset1, axiom,
% 6.02/6.20    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.02/6.20     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 6.02/6.20       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 6.02/6.20  thf('8', plain,
% 6.02/6.20      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 6.02/6.20         ((k5_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)
% 6.02/6.20           = (k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39))),
% 6.02/6.20      inference('cnf', [status(esa)], [t74_enumset1])).
% 6.02/6.20  thf(t68_enumset1, axiom,
% 6.02/6.20    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 6.02/6.20     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 6.02/6.20       ( k2_xboole_0 @
% 6.02/6.20         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 6.02/6.20  thf('9', plain,
% 6.02/6.20      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, 
% 6.02/6.20         X18 : $i]:
% 6.02/6.20         ((k6_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18)
% 6.02/6.20           = (k2_xboole_0 @ 
% 6.02/6.20              (k5_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17) @ 
% 6.02/6.20              (k1_tarski @ X18)))),
% 6.02/6.20      inference('cnf', [status(esa)], [t68_enumset1])).
% 6.02/6.20  thf('10', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 6.02/6.20         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 6.02/6.20           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 6.02/6.20              (k1_tarski @ X6)))),
% 6.02/6.20      inference('sup+', [status(thm)], ['8', '9'])).
% 6.02/6.20  thf(t75_enumset1, axiom,
% 6.02/6.20    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 6.02/6.20     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 6.02/6.20       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 6.02/6.20  thf('11', plain,
% 6.02/6.20      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 6.02/6.20         ((k6_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 6.02/6.20           = (k5_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46))),
% 6.02/6.20      inference('cnf', [status(esa)], [t75_enumset1])).
% 6.02/6.20  thf('12', plain,
% 6.02/6.20      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 6.02/6.20         ((k5_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)
% 6.02/6.20           = (k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39))),
% 6.02/6.20      inference('cnf', [status(esa)], [t74_enumset1])).
% 6.02/6.20  thf('13', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 6.02/6.20         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 6.02/6.20           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 6.02/6.20      inference('sup+', [status(thm)], ['11', '12'])).
% 6.02/6.20  thf('14', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 6.02/6.20         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 6.02/6.20           (k1_tarski @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 6.02/6.20      inference('sup+', [status(thm)], ['10', '13'])).
% 6.02/6.20  thf(t73_enumset1, axiom,
% 6.02/6.20    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.02/6.20     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 6.02/6.20       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 6.02/6.20  thf('15', plain,
% 6.02/6.20      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 6.02/6.20         ((k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33)
% 6.02/6.20           = (k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 6.02/6.20      inference('cnf', [status(esa)], [t73_enumset1])).
% 6.02/6.20  thf('16', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 6.02/6.20         ((k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 6.02/6.20           (k1_tarski @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 6.02/6.20      inference('demod', [status(thm)], ['14', '15'])).
% 6.02/6.20  thf('17', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.02/6.20         ((k2_xboole_0 @ (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) @ 
% 6.02/6.20           (k1_tarski @ X3)) = (k4_enumset1 @ X2 @ X2 @ X2 @ X0 @ X1 @ X3))),
% 6.02/6.20      inference('sup+', [status(thm)], ['7', '16'])).
% 6.02/6.20  thf('18', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 6.02/6.20         ((k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 6.02/6.20           (k1_tarski @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 6.02/6.20      inference('demod', [status(thm)], ['14', '15'])).
% 6.02/6.20  thf('19', plain,
% 6.02/6.20      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 6.02/6.20         ((k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33)
% 6.02/6.20           = (k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 6.02/6.20      inference('cnf', [status(esa)], [t73_enumset1])).
% 6.02/6.20  thf('20', plain,
% 6.02/6.20      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 6.02/6.20         ((k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33)
% 6.02/6.20           = (k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 6.02/6.20      inference('cnf', [status(esa)], [t73_enumset1])).
% 6.02/6.20  thf('21', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.02/6.20         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 6.02/6.20           = (k3_enumset1 @ X2 @ X2 @ X0 @ X1 @ X3))),
% 6.02/6.20      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 6.02/6.20  thf('22', plain,
% 6.02/6.20      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 6.02/6.20         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 6.02/6.20           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 6.02/6.20      inference('cnf', [status(esa)], [t72_enumset1])).
% 6.02/6.20  thf('23', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.02/6.20         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 6.02/6.20           = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 6.02/6.20      inference('sup+', [status(thm)], ['21', '22'])).
% 6.02/6.20  thf('24', plain,
% 6.02/6.20      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 6.02/6.20         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 6.02/6.20           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 6.02/6.20      inference('cnf', [status(esa)], [t72_enumset1])).
% 6.02/6.20  thf('25', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.02/6.20         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 6.02/6.20      inference('sup+', [status(thm)], ['23', '24'])).
% 6.02/6.20  thf('26', plain,
% 6.02/6.20      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 6.02/6.20         (k2_tarski @ sk_D @ sk_E))
% 6.02/6.20         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_D) @ 
% 6.02/6.20             (k3_mcart_1 @ sk_A @ sk_B @ sk_E) @ 
% 6.02/6.20             (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 6.02/6.20             (k3_mcart_1 @ sk_A @ sk_C @ sk_E)))),
% 6.02/6.20      inference('demod', [status(thm)], ['0', '25'])).
% 6.02/6.20  thf(d3_mcart_1, axiom,
% 6.02/6.20    (![A:$i,B:$i,C:$i]:
% 6.02/6.20     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 6.02/6.20  thf('27', plain,
% 6.02/6.20      (![X60 : $i, X61 : $i, X62 : $i]:
% 6.02/6.20         ((k3_mcart_1 @ X60 @ X61 @ X62)
% 6.02/6.20           = (k4_tarski @ (k4_tarski @ X60 @ X61) @ X62))),
% 6.02/6.20      inference('cnf', [status(esa)], [d3_mcart_1])).
% 6.02/6.20  thf('28', plain,
% 6.02/6.20      (![X60 : $i, X61 : $i, X62 : $i]:
% 6.02/6.20         ((k3_mcart_1 @ X60 @ X61 @ X62)
% 6.02/6.20           = (k4_tarski @ (k4_tarski @ X60 @ X61) @ X62))),
% 6.02/6.20      inference('cnf', [status(esa)], [d3_mcart_1])).
% 6.02/6.20  thf(t146_zfmisc_1, axiom,
% 6.02/6.20    (![A:$i,B:$i,C:$i,D:$i]:
% 6.02/6.20     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 6.02/6.20       ( k2_enumset1 @
% 6.02/6.20         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 6.02/6.20         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 6.02/6.20  thf('29', plain,
% 6.02/6.20      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 6.02/6.20         ((k2_zfmisc_1 @ (k2_tarski @ X52 @ X55) @ (k2_tarski @ X53 @ X54))
% 6.02/6.20           = (k2_enumset1 @ (k4_tarski @ X52 @ X53) @ 
% 6.02/6.20              (k4_tarski @ X52 @ X54) @ (k4_tarski @ X55 @ X53) @ 
% 6.02/6.20              (k4_tarski @ X55 @ X54)))),
% 6.02/6.20      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 6.02/6.20  thf('30', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.02/6.20         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 6.02/6.20           (k2_tarski @ X0 @ X3))
% 6.02/6.20           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 6.02/6.20              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 6.02/6.20              (k4_tarski @ X4 @ X0) @ (k4_tarski @ X4 @ X3)))),
% 6.02/6.20      inference('sup+', [status(thm)], ['28', '29'])).
% 6.02/6.20  thf('31', plain,
% 6.02/6.20      (![X60 : $i, X61 : $i, X62 : $i]:
% 6.02/6.20         ((k3_mcart_1 @ X60 @ X61 @ X62)
% 6.02/6.20           = (k4_tarski @ (k4_tarski @ X60 @ X61) @ X62))),
% 6.02/6.20      inference('cnf', [status(esa)], [d3_mcart_1])).
% 6.02/6.20  thf('32', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.02/6.20         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 6.02/6.20           (k2_tarski @ X0 @ X3))
% 6.02/6.20           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 6.02/6.20              (k3_mcart_1 @ X2 @ X1 @ X3) @ (k4_tarski @ X4 @ X0) @ 
% 6.02/6.20              (k4_tarski @ X4 @ X3)))),
% 6.02/6.20      inference('demod', [status(thm)], ['30', '31'])).
% 6.02/6.20  thf('33', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 6.02/6.20         ((k2_zfmisc_1 @ 
% 6.02/6.20           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 6.02/6.20           (k2_tarski @ X0 @ X3))
% 6.02/6.20           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 6.02/6.20              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 6.02/6.20              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3)))),
% 6.02/6.20      inference('sup+', [status(thm)], ['27', '32'])).
% 6.02/6.20  thf('34', plain,
% 6.02/6.20      (![X60 : $i, X61 : $i, X62 : $i]:
% 6.02/6.20         ((k3_mcart_1 @ X60 @ X61 @ X62)
% 6.02/6.20           = (k4_tarski @ (k4_tarski @ X60 @ X61) @ X62))),
% 6.02/6.20      inference('cnf', [status(esa)], [d3_mcart_1])).
% 6.02/6.20  thf('35', plain,
% 6.02/6.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 6.02/6.20         ((k2_zfmisc_1 @ 
% 6.02/6.20           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 6.02/6.20           (k2_tarski @ X0 @ X3))
% 6.02/6.20           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 6.02/6.20              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 6.02/6.20              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 6.02/6.20      inference('demod', [status(thm)], ['33', '34'])).
% 6.02/6.20  thf(t36_zfmisc_1, axiom,
% 6.02/6.20    (![A:$i,B:$i,C:$i]:
% 6.02/6.20     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 6.02/6.20         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 6.02/6.20       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 6.02/6.20         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 6.02/6.20  thf('36', plain,
% 6.02/6.20      (![X56 : $i, X57 : $i, X58 : $i]:
% 6.02/6.20         ((k2_zfmisc_1 @ (k1_tarski @ X56) @ (k2_tarski @ X57 @ X58))
% 6.02/6.20           = (k2_tarski @ (k4_tarski @ X56 @ X57) @ (k4_tarski @ X56 @ X58)))),
% 6.02/6.20      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 6.02/6.20  thf(d3_zfmisc_1, axiom,
% 6.02/6.20    (![A:$i,B:$i,C:$i]:
% 6.02/6.20     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 6.02/6.20       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 6.02/6.20  thf('37', plain,
% 6.02/6.20      (![X63 : $i, X64 : $i, X65 : $i]:
% 6.02/6.20         ((k3_zfmisc_1 @ X63 @ X64 @ X65)
% 6.02/6.20           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X64) @ X65))),
% 6.02/6.20      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 6.02/6.20  thf('38', plain,
% 6.02/6.20      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 6.02/6.20         (k2_tarski @ sk_D @ sk_E))
% 6.02/6.20         != (k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 6.02/6.20             (k2_tarski @ sk_D @ sk_E)))),
% 6.02/6.20      inference('demod', [status(thm)], ['26', '35', '36', '37'])).
% 6.02/6.20  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 6.02/6.20  
% 6.02/6.20  % SZS output end Refutation
% 6.02/6.20  
% 6.02/6.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
