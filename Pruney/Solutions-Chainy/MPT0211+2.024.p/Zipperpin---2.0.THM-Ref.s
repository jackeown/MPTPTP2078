%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Rhr8vM2QU2

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:33 EST 2020

% Result     : Theorem 24.37s
% Output     : Refutation 24.37s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 339 expanded)
%              Number of leaves         :   20 ( 121 expanded)
%              Depth                    :   12
%              Number of atoms          :  814 (3706 expanded)
%              Number of equality atoms :   73 ( 328 expanded)
%              Maximal formula depth    :   14 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

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

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X21 @ X20 @ X19 @ X18 )
      = ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 ) @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t113_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X13 @ X10 @ X12 @ X11 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf('10',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('12',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X0 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('17',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X8 @ X7 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('19',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X8 @ X7 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X2 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('32',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('33',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['25','30','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['25','30','35'])).

thf('38',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','22'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','22'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('47',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t54_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) )).

thf('50',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X27 @ X28 @ X29 @ X30 ) @ ( k2_tarski @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X0 ) @ ( k2_tarski @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['25','30','35'])).

thf('55',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X21 @ X20 @ X19 @ X18 )
      = ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['38','53','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Rhr8vM2QU2
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 24.37/24.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 24.37/24.57  % Solved by: fo/fo7.sh
% 24.37/24.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 24.37/24.57  % done 23751 iterations in 24.120s
% 24.37/24.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 24.37/24.57  % SZS output start Refutation
% 24.37/24.57  thf(sk_B_type, type, sk_B: $i).
% 24.37/24.57  thf(sk_A_type, type, sk_A: $i).
% 24.37/24.57  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 24.37/24.57  thf(sk_C_type, type, sk_C: $i).
% 24.37/24.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 24.37/24.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 24.37/24.57  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 24.37/24.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 24.37/24.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 24.37/24.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 24.37/24.57  thf(t137_enumset1, conjecture,
% 24.37/24.57    (![A:$i,B:$i,C:$i]:
% 24.37/24.57     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 24.37/24.57       ( k1_enumset1 @ A @ B @ C ) ))).
% 24.37/24.57  thf(zf_stmt_0, negated_conjecture,
% 24.37/24.57    (~( ![A:$i,B:$i,C:$i]:
% 24.37/24.57        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 24.37/24.57          ( k1_enumset1 @ A @ B @ C ) ) )),
% 24.37/24.57    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 24.37/24.57  thf('0', plain,
% 24.37/24.57      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 24.37/24.57         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 24.37/24.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.37/24.57  thf(t125_enumset1, axiom,
% 24.37/24.57    (![A:$i,B:$i,C:$i,D:$i]:
% 24.37/24.57     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 24.37/24.57  thf('1', plain,
% 24.37/24.57      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X21 @ X20 @ X19 @ X18)
% 24.37/24.57           = (k2_enumset1 @ X18 @ X19 @ X20 @ X21))),
% 24.37/24.57      inference('cnf', [status(esa)], [t125_enumset1])).
% 24.37/24.57  thf(t71_enumset1, axiom,
% 24.37/24.57    (![A:$i,B:$i,C:$i]:
% 24.37/24.57     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 24.37/24.57  thf('2', plain,
% 24.37/24.57      (![X36 : $i, X37 : $i, X38 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 24.37/24.57           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 24.37/24.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 24.37/24.57  thf('3', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 24.37/24.57      inference('sup+', [status(thm)], ['1', '2'])).
% 24.37/24.57  thf('4', plain,
% 24.37/24.57      (![X36 : $i, X37 : $i, X38 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 24.37/24.57           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 24.37/24.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 24.37/24.57  thf('5', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i]:
% 24.37/24.57         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 24.37/24.57      inference('sup+', [status(thm)], ['3', '4'])).
% 24.37/24.57  thf('6', plain,
% 24.37/24.57      (![X36 : $i, X37 : $i, X38 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 24.37/24.57           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 24.37/24.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 24.37/24.57  thf(t50_enumset1, axiom,
% 24.37/24.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 24.37/24.57     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 24.37/24.57       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 24.37/24.57  thf('7', plain,
% 24.37/24.57      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26)
% 24.37/24.57           = (k2_xboole_0 @ (k2_enumset1 @ X22 @ X23 @ X24 @ X25) @ 
% 24.37/24.57              (k1_tarski @ X26)))),
% 24.37/24.57      inference('cnf', [status(esa)], [t50_enumset1])).
% 24.37/24.57  thf('8', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 24.37/24.57           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 24.37/24.57      inference('sup+', [status(thm)], ['6', '7'])).
% 24.37/24.57  thf(t113_enumset1, axiom,
% 24.37/24.57    (![A:$i,B:$i,C:$i,D:$i]:
% 24.37/24.57     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 24.37/24.57  thf('9', plain,
% 24.37/24.57      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X13 @ X10 @ X12 @ X11)
% 24.37/24.57           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 24.37/24.57      inference('cnf', [status(esa)], [t113_enumset1])).
% 24.37/24.57  thf('10', plain,
% 24.37/24.57      (![X36 : $i, X37 : $i, X38 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 24.37/24.57           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 24.37/24.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 24.37/24.57  thf('11', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 24.37/24.57      inference('sup+', [status(thm)], ['9', '10'])).
% 24.37/24.57  thf(t72_enumset1, axiom,
% 24.37/24.57    (![A:$i,B:$i,C:$i,D:$i]:
% 24.37/24.57     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 24.37/24.57  thf('12', plain,
% 24.37/24.57      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 24.37/24.57           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 24.37/24.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 24.37/24.57  thf('13', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 24.37/24.57      inference('sup+', [status(thm)], ['11', '12'])).
% 24.37/24.57  thf('14', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X0 @ X1) @ (k1_tarski @ X0))
% 24.37/24.57           = (k1_enumset1 @ X0 @ X1 @ X2))),
% 24.37/24.57      inference('sup+', [status(thm)], ['8', '13'])).
% 24.37/24.57  thf('15', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i]:
% 24.37/24.57         ((k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X0) @ (k1_tarski @ X1))
% 24.37/24.57           = (k1_enumset1 @ X1 @ X1 @ X0))),
% 24.37/24.57      inference('sup+', [status(thm)], ['5', '14'])).
% 24.37/24.57  thf('16', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 24.37/24.57           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 24.37/24.57      inference('sup+', [status(thm)], ['6', '7'])).
% 24.37/24.57  thf('17', plain,
% 24.37/24.57      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 24.37/24.57           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 24.37/24.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 24.37/24.57  thf(t107_enumset1, axiom,
% 24.37/24.57    (![A:$i,B:$i,C:$i,D:$i]:
% 24.37/24.57     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 24.37/24.57  thf('18', plain,
% 24.37/24.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X6 @ X9 @ X8 @ X7) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 24.37/24.57      inference('cnf', [status(esa)], [t107_enumset1])).
% 24.37/24.57  thf('19', plain,
% 24.37/24.57      (![X36 : $i, X37 : $i, X38 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 24.37/24.57           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 24.37/24.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 24.37/24.57  thf('20', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 24.37/24.57      inference('sup+', [status(thm)], ['18', '19'])).
% 24.37/24.57  thf('21', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 24.37/24.57      inference('sup+', [status(thm)], ['17', '20'])).
% 24.37/24.57  thf('22', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k2_xboole_0 @ (k1_enumset1 @ X0 @ X2 @ X1) @ (k1_tarski @ X0))
% 24.37/24.57           = (k1_enumset1 @ X0 @ X1 @ X2))),
% 24.37/24.57      inference('sup+', [status(thm)], ['16', '21'])).
% 24.37/24.57  thf('23', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i]:
% 24.37/24.57         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 24.37/24.57      inference('demod', [status(thm)], ['15', '22'])).
% 24.37/24.57  thf('24', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 24.37/24.57           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 24.37/24.57      inference('sup+', [status(thm)], ['6', '7'])).
% 24.37/24.57  thf('25', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X1 @ X1 @ X0 @ X0 @ X2)
% 24.37/24.57           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 24.37/24.57      inference('sup+', [status(thm)], ['23', '24'])).
% 24.37/24.57  thf('26', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 24.37/24.57      inference('sup+', [status(thm)], ['1', '2'])).
% 24.37/24.57  thf('27', plain,
% 24.37/24.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X6 @ X9 @ X8 @ X7) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 24.37/24.57      inference('cnf', [status(esa)], [t107_enumset1])).
% 24.37/24.57  thf('28', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X0 @ X2 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 24.37/24.57      inference('sup+', [status(thm)], ['26', '27'])).
% 24.37/24.57  thf('29', plain,
% 24.37/24.57      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 24.37/24.57           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 24.37/24.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 24.37/24.57  thf('30', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X0 @ X0 @ X2 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 24.37/24.57      inference('sup+', [status(thm)], ['28', '29'])).
% 24.37/24.57  thf('31', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 24.37/24.57           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 24.37/24.57      inference('sup+', [status(thm)], ['6', '7'])).
% 24.37/24.57  thf('32', plain,
% 24.37/24.57      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 24.37/24.57           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 24.37/24.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 24.37/24.57  thf('33', plain,
% 24.37/24.57      (![X36 : $i, X37 : $i, X38 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 24.37/24.57           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 24.37/24.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 24.37/24.57  thf('34', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 24.37/24.57      inference('sup+', [status(thm)], ['32', '33'])).
% 24.37/24.57  thf('35', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0))
% 24.37/24.57           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 24.37/24.57      inference('sup+', [status(thm)], ['31', '34'])).
% 24.37/24.57  thf('36', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k1_enumset1 @ X0 @ X2 @ X1) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 24.37/24.57      inference('demod', [status(thm)], ['25', '30', '35'])).
% 24.37/24.57  thf('37', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k1_enumset1 @ X0 @ X2 @ X1) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 24.37/24.57      inference('demod', [status(thm)], ['25', '30', '35'])).
% 24.37/24.57  thf('38', plain,
% 24.37/24.57      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 24.37/24.57         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 24.37/24.57      inference('demod', [status(thm)], ['0', '36', '37'])).
% 24.37/24.57  thf('39', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i]:
% 24.37/24.57         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 24.37/24.57      inference('demod', [status(thm)], ['15', '22'])).
% 24.37/24.57  thf(t70_enumset1, axiom,
% 24.37/24.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 24.37/24.57  thf('40', plain,
% 24.37/24.57      (![X34 : $i, X35 : $i]:
% 24.37/24.57         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 24.37/24.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 24.37/24.57  thf('41', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i]:
% 24.37/24.57         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 24.37/24.57      inference('sup+', [status(thm)], ['39', '40'])).
% 24.37/24.57  thf('42', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i]:
% 24.37/24.57         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 24.37/24.57      inference('sup+', [status(thm)], ['3', '4'])).
% 24.37/24.57  thf('43', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i]:
% 24.37/24.57         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 24.37/24.57      inference('sup+', [status(thm)], ['41', '42'])).
% 24.37/24.57  thf('44', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i]:
% 24.37/24.57         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 24.37/24.57      inference('demod', [status(thm)], ['15', '22'])).
% 24.37/24.57  thf('45', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i]:
% 24.37/24.57         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 24.37/24.57      inference('sup+', [status(thm)], ['43', '44'])).
% 24.37/24.57  thf('46', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 24.37/24.57      inference('sup+', [status(thm)], ['17', '20'])).
% 24.37/24.57  thf(t73_enumset1, axiom,
% 24.37/24.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 24.37/24.57     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 24.37/24.57       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 24.37/24.57  thf('47', plain,
% 24.37/24.57      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 24.37/24.57         ((k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47)
% 24.37/24.57           = (k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 24.37/24.57      inference('cnf', [status(esa)], [t73_enumset1])).
% 24.37/24.57  thf('48', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k4_enumset1 @ X2 @ X2 @ X2 @ X0 @ X1 @ X2)
% 24.37/24.57           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 24.37/24.57      inference('sup+', [status(thm)], ['46', '47'])).
% 24.37/24.57  thf('49', plain,
% 24.37/24.57      (![X36 : $i, X37 : $i, X38 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 24.37/24.57           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 24.37/24.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 24.37/24.57  thf(t54_enumset1, axiom,
% 24.37/24.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 24.37/24.57     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 24.37/24.57       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ))).
% 24.37/24.57  thf('50', plain,
% 24.37/24.57      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 24.37/24.57         ((k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 24.37/24.57           = (k2_xboole_0 @ (k2_enumset1 @ X27 @ X28 @ X29 @ X30) @ 
% 24.37/24.57              (k2_tarski @ X31 @ X32)))),
% 24.37/24.57      inference('cnf', [status(esa)], [t54_enumset1])).
% 24.37/24.57  thf('51', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 24.37/24.57         ((k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 24.37/24.57           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 24.37/24.57              (k2_tarski @ X4 @ X3)))),
% 24.37/24.57      inference('sup+', [status(thm)], ['49', '50'])).
% 24.37/24.57  thf('52', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k1_enumset1 @ X2 @ X1 @ X0)
% 24.37/24.57           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X0) @ 
% 24.37/24.57              (k2_tarski @ X1 @ X2)))),
% 24.37/24.57      inference('sup+', [status(thm)], ['48', '51'])).
% 24.37/24.57  thf('53', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k1_enumset1 @ X0 @ X2 @ X1)
% 24.37/24.57           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X2 @ X0)))),
% 24.37/24.57      inference('sup+', [status(thm)], ['45', '52'])).
% 24.37/24.57  thf('54', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k1_enumset1 @ X0 @ X2 @ X1) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 24.37/24.57      inference('demod', [status(thm)], ['25', '30', '35'])).
% 24.37/24.57  thf('55', plain,
% 24.37/24.57      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X21 @ X20 @ X19 @ X18)
% 24.37/24.57           = (k2_enumset1 @ X18 @ X19 @ X20 @ X21))),
% 24.37/24.57      inference('cnf', [status(esa)], [t125_enumset1])).
% 24.37/24.57  thf('56', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 24.37/24.57      inference('sup+', [status(thm)], ['18', '19'])).
% 24.37/24.57  thf('57', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 24.37/24.57      inference('sup+', [status(thm)], ['55', '56'])).
% 24.37/24.57  thf('58', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 24.37/24.57      inference('sup+', [status(thm)], ['18', '19'])).
% 24.37/24.57  thf('59', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 24.37/24.57      inference('sup+', [status(thm)], ['57', '58'])).
% 24.37/24.57  thf('60', plain,
% 24.37/24.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.37/24.57         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 24.37/24.57      inference('sup+', [status(thm)], ['54', '59'])).
% 24.37/24.57  thf('61', plain,
% 24.37/24.57      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 24.37/24.57         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 24.37/24.57      inference('demod', [status(thm)], ['38', '53', '60'])).
% 24.37/24.57  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 24.37/24.57  
% 24.37/24.57  % SZS output end Refutation
% 24.37/24.57  
% 24.37/24.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
