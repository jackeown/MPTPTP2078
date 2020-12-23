%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SZWwFkFgqL

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:15 EST 2020

% Result     : Theorem 7.30s
% Output     : Refutation 7.30s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 133 expanded)
%              Number of leaves         :   40 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  864 (1082 expanded)
%              Number of equality atoms :   97 ( 123 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','22'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('28',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X45 @ X46 )
      = ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('31',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k5_enumset1 @ X56 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 )
      = ( k4_enumset1 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('32',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k4_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k3_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k4_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k3_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('35',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k5_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 ) @ ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('38',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 )
      = ( k2_enumset1 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 )
      = ( k2_enumset1 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X45 @ X46 )
      = ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('44',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X33 @ X32 @ X31 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X45 @ X46 )
      = ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('48',plain,(
    ! [X69: $i,X70: $i,X71: $i] :
      ( ( k1_enumset1 @ X69 @ X71 @ X70 )
      = ( k1_enumset1 @ X69 @ X70 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('49',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X33 @ X32 @ X31 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X45 @ X46 )
      = ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('54',plain,(
    ! [X69: $i,X70: $i,X71: $i] :
      ( ( k1_enumset1 @ X69 @ X71 @ X70 )
      = ( k1_enumset1 @ X69 @ X70 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('55',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['27','42','47','52','53','54'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['55','57'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('59',plain,(
    ! [X25: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X27 )
      | ( X29 = X28 )
      | ( X29 = X25 )
      | ( X27
       != ( k2_tarski @ X28 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('60',plain,(
    ! [X25: $i,X28: $i,X29: $i] :
      ( ( X29 = X25 )
      | ( X29 = X28 )
      | ~ ( r2_hidden @ X29 @ ( k2_tarski @ X28 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( X0 = sk_B )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('63',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SZWwFkFgqL
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:34:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 7.30/7.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.30/7.51  % Solved by: fo/fo7.sh
% 7.30/7.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.30/7.51  % done 5971 iterations in 7.049s
% 7.30/7.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.30/7.51  % SZS output start Refutation
% 7.30/7.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.30/7.51  thf(sk_B_type, type, sk_B: $i).
% 7.30/7.51  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 7.30/7.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 7.30/7.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 7.30/7.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.30/7.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.30/7.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 7.30/7.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 7.30/7.51  thf(sk_C_type, type, sk_C: $i).
% 7.30/7.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.30/7.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.30/7.51  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 7.30/7.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.30/7.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.30/7.51  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 7.30/7.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.30/7.51  thf(sk_A_type, type, sk_A: $i).
% 7.30/7.51  thf(t25_zfmisc_1, conjecture,
% 7.30/7.51    (![A:$i,B:$i,C:$i]:
% 7.30/7.51     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 7.30/7.51          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 7.30/7.51  thf(zf_stmt_0, negated_conjecture,
% 7.30/7.51    (~( ![A:$i,B:$i,C:$i]:
% 7.30/7.51        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 7.30/7.51             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 7.30/7.51    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 7.30/7.51  thf('0', plain,
% 7.30/7.51      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 7.30/7.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.51  thf(t28_xboole_1, axiom,
% 7.30/7.51    (![A:$i,B:$i]:
% 7.30/7.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 7.30/7.51  thf('1', plain,
% 7.30/7.51      (![X5 : $i, X6 : $i]:
% 7.30/7.51         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 7.30/7.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 7.30/7.51  thf('2', plain,
% 7.30/7.51      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 7.30/7.51         = (k1_tarski @ sk_A))),
% 7.30/7.51      inference('sup-', [status(thm)], ['0', '1'])).
% 7.30/7.51  thf(t100_xboole_1, axiom,
% 7.30/7.51    (![A:$i,B:$i]:
% 7.30/7.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 7.30/7.51  thf('3', plain,
% 7.30/7.51      (![X3 : $i, X4 : $i]:
% 7.30/7.51         ((k4_xboole_0 @ X3 @ X4)
% 7.30/7.51           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 7.30/7.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.30/7.51  thf('4', plain,
% 7.30/7.51      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 7.30/7.51         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 7.30/7.51      inference('sup+', [status(thm)], ['2', '3'])).
% 7.30/7.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 7.30/7.51  thf('5', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 7.30/7.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 7.30/7.51  thf('6', plain,
% 7.30/7.51      (![X5 : $i, X6 : $i]:
% 7.30/7.51         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 7.30/7.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 7.30/7.51  thf('7', plain,
% 7.30/7.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 7.30/7.51      inference('sup-', [status(thm)], ['5', '6'])).
% 7.30/7.51  thf(commutativity_k3_xboole_0, axiom,
% 7.30/7.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 7.30/7.51  thf('8', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.30/7.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.30/7.51  thf('9', plain,
% 7.30/7.51      (![X3 : $i, X4 : $i]:
% 7.30/7.51         ((k4_xboole_0 @ X3 @ X4)
% 7.30/7.51           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 7.30/7.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.30/7.51  thf('10', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i]:
% 7.30/7.51         ((k4_xboole_0 @ X0 @ X1)
% 7.30/7.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 7.30/7.51      inference('sup+', [status(thm)], ['8', '9'])).
% 7.30/7.51  thf('11', plain,
% 7.30/7.51      (![X0 : $i]:
% 7.30/7.51         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 7.30/7.51      inference('sup+', [status(thm)], ['7', '10'])).
% 7.30/7.51  thf(t5_boole, axiom,
% 7.30/7.51    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 7.30/7.51  thf('12', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 7.30/7.51      inference('cnf', [status(esa)], [t5_boole])).
% 7.30/7.51  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 7.30/7.51      inference('demod', [status(thm)], ['11', '12'])).
% 7.30/7.51  thf(t48_xboole_1, axiom,
% 7.30/7.51    (![A:$i,B:$i]:
% 7.30/7.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 7.30/7.51  thf('14', plain,
% 7.30/7.51      (![X8 : $i, X9 : $i]:
% 7.30/7.51         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 7.30/7.51           = (k3_xboole_0 @ X8 @ X9))),
% 7.30/7.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.30/7.51  thf('15', plain,
% 7.30/7.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 7.30/7.51      inference('sup+', [status(thm)], ['13', '14'])).
% 7.30/7.51  thf(idempotence_k3_xboole_0, axiom,
% 7.30/7.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 7.30/7.51  thf('16', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 7.30/7.51      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 7.30/7.51  thf('17', plain,
% 7.30/7.51      (![X3 : $i, X4 : $i]:
% 7.30/7.51         ((k4_xboole_0 @ X3 @ X4)
% 7.30/7.51           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 7.30/7.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.30/7.51  thf('18', plain,
% 7.30/7.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 7.30/7.51      inference('sup+', [status(thm)], ['16', '17'])).
% 7.30/7.51  thf('19', plain,
% 7.30/7.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 7.30/7.51      inference('sup-', [status(thm)], ['5', '6'])).
% 7.30/7.51  thf('20', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.30/7.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.30/7.51  thf('21', plain,
% 7.30/7.51      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 7.30/7.51      inference('sup+', [status(thm)], ['19', '20'])).
% 7.30/7.51  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 7.30/7.51      inference('demod', [status(thm)], ['15', '18', '21'])).
% 7.30/7.51  thf('23', plain,
% 7.30/7.51      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 7.30/7.51         = (k1_xboole_0))),
% 7.30/7.51      inference('demod', [status(thm)], ['4', '22'])).
% 7.30/7.51  thf(t98_xboole_1, axiom,
% 7.30/7.51    (![A:$i,B:$i]:
% 7.30/7.51     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 7.30/7.51  thf('24', plain,
% 7.30/7.51      (![X11 : $i, X12 : $i]:
% 7.30/7.51         ((k2_xboole_0 @ X11 @ X12)
% 7.30/7.51           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 7.30/7.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 7.30/7.51  thf('25', plain,
% 7.30/7.51      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 7.30/7.51         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 7.30/7.51      inference('sup+', [status(thm)], ['23', '24'])).
% 7.30/7.51  thf('26', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 7.30/7.51      inference('cnf', [status(esa)], [t5_boole])).
% 7.30/7.51  thf('27', plain,
% 7.30/7.51      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 7.30/7.51         = (k2_tarski @ sk_B @ sk_C))),
% 7.30/7.51      inference('demod', [status(thm)], ['25', '26'])).
% 7.30/7.51  thf(t71_enumset1, axiom,
% 7.30/7.51    (![A:$i,B:$i,C:$i]:
% 7.30/7.51     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 7.30/7.51  thf('28', plain,
% 7.30/7.51      (![X44 : $i, X45 : $i, X46 : $i]:
% 7.30/7.51         ((k2_enumset1 @ X44 @ X44 @ X45 @ X46)
% 7.30/7.51           = (k1_enumset1 @ X44 @ X45 @ X46))),
% 7.30/7.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.30/7.51  thf(t70_enumset1, axiom,
% 7.30/7.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 7.30/7.51  thf('29', plain,
% 7.30/7.51      (![X42 : $i, X43 : $i]:
% 7.30/7.51         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 7.30/7.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.30/7.51  thf('30', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i]:
% 7.30/7.51         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 7.30/7.51      inference('sup+', [status(thm)], ['28', '29'])).
% 7.30/7.51  thf(t74_enumset1, axiom,
% 7.30/7.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 7.30/7.51     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 7.30/7.51       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 7.30/7.51  thf('31', plain,
% 7.30/7.51      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 7.30/7.51         ((k5_enumset1 @ X56 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61)
% 7.30/7.51           = (k4_enumset1 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61))),
% 7.30/7.51      inference('cnf', [status(esa)], [t74_enumset1])).
% 7.30/7.51  thf(t73_enumset1, axiom,
% 7.30/7.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 7.30/7.51     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 7.30/7.51       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 7.30/7.51  thf('32', plain,
% 7.30/7.51      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 7.30/7.51         ((k4_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55)
% 7.30/7.51           = (k3_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 7.30/7.51      inference('cnf', [status(esa)], [t73_enumset1])).
% 7.30/7.51  thf('33', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 7.30/7.51         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 7.30/7.51           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 7.30/7.51      inference('sup+', [status(thm)], ['31', '32'])).
% 7.30/7.51  thf('34', plain,
% 7.30/7.51      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 7.30/7.51         ((k4_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55)
% 7.30/7.51           = (k3_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 7.30/7.51      inference('cnf', [status(esa)], [t73_enumset1])).
% 7.30/7.51  thf(t61_enumset1, axiom,
% 7.30/7.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 7.30/7.51     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 7.30/7.51       ( k2_xboole_0 @
% 7.30/7.51         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 7.30/7.51  thf('35', plain,
% 7.30/7.51      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 7.30/7.51         ((k5_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 7.30/7.51           = (k2_xboole_0 @ 
% 7.30/7.51              (k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39) @ 
% 7.30/7.51              (k1_tarski @ X40)))),
% 7.30/7.51      inference('cnf', [status(esa)], [t61_enumset1])).
% 7.30/7.51  thf('36', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 7.30/7.51         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 7.30/7.51           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 7.30/7.51              (k1_tarski @ X5)))),
% 7.30/7.51      inference('sup+', [status(thm)], ['34', '35'])).
% 7.30/7.51  thf('37', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 7.30/7.51         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 7.30/7.51           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 7.30/7.51              (k1_tarski @ X0)))),
% 7.30/7.51      inference('sup+', [status(thm)], ['33', '36'])).
% 7.30/7.51  thf(t72_enumset1, axiom,
% 7.30/7.51    (![A:$i,B:$i,C:$i,D:$i]:
% 7.30/7.51     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 7.30/7.51  thf('38', plain,
% 7.30/7.51      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 7.30/7.51         ((k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50)
% 7.30/7.51           = (k2_enumset1 @ X47 @ X48 @ X49 @ X50))),
% 7.30/7.51      inference('cnf', [status(esa)], [t72_enumset1])).
% 7.30/7.51  thf('39', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 7.30/7.51         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 7.30/7.51           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 7.30/7.51              (k1_tarski @ X0)))),
% 7.30/7.51      inference('demod', [status(thm)], ['37', '38'])).
% 7.30/7.51  thf('40', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.30/7.51         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 7.30/7.51           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 7.30/7.51      inference('sup+', [status(thm)], ['30', '39'])).
% 7.30/7.51  thf('41', plain,
% 7.30/7.51      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 7.30/7.51         ((k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50)
% 7.30/7.51           = (k2_enumset1 @ X47 @ X48 @ X49 @ X50))),
% 7.30/7.51      inference('cnf', [status(esa)], [t72_enumset1])).
% 7.30/7.51  thf('42', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.30/7.51         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 7.30/7.51           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 7.30/7.51      inference('demod', [status(thm)], ['40', '41'])).
% 7.30/7.51  thf('43', plain,
% 7.30/7.51      (![X44 : $i, X45 : $i, X46 : $i]:
% 7.30/7.51         ((k2_enumset1 @ X44 @ X44 @ X45 @ X46)
% 7.30/7.51           = (k1_enumset1 @ X44 @ X45 @ X46))),
% 7.30/7.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.30/7.51  thf(t102_enumset1, axiom,
% 7.30/7.51    (![A:$i,B:$i,C:$i]:
% 7.30/7.51     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 7.30/7.51  thf('44', plain,
% 7.30/7.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.30/7.51         ((k1_enumset1 @ X33 @ X32 @ X31) = (k1_enumset1 @ X31 @ X32 @ X33))),
% 7.30/7.51      inference('cnf', [status(esa)], [t102_enumset1])).
% 7.30/7.51  thf('45', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.30/7.51         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 7.30/7.51      inference('sup+', [status(thm)], ['43', '44'])).
% 7.30/7.51  thf('46', plain,
% 7.30/7.51      (![X44 : $i, X45 : $i, X46 : $i]:
% 7.30/7.51         ((k2_enumset1 @ X44 @ X44 @ X45 @ X46)
% 7.30/7.51           = (k1_enumset1 @ X44 @ X45 @ X46))),
% 7.30/7.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.30/7.51  thf('47', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.30/7.51         ((k2_enumset1 @ X0 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 7.30/7.51      inference('sup+', [status(thm)], ['45', '46'])).
% 7.30/7.51  thf(t98_enumset1, axiom,
% 7.30/7.51    (![A:$i,B:$i,C:$i]:
% 7.30/7.51     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 7.30/7.51  thf('48', plain,
% 7.30/7.51      (![X69 : $i, X70 : $i, X71 : $i]:
% 7.30/7.51         ((k1_enumset1 @ X69 @ X71 @ X70) = (k1_enumset1 @ X69 @ X70 @ X71))),
% 7.30/7.51      inference('cnf', [status(esa)], [t98_enumset1])).
% 7.30/7.51  thf('49', plain,
% 7.30/7.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.30/7.51         ((k1_enumset1 @ X33 @ X32 @ X31) = (k1_enumset1 @ X31 @ X32 @ X33))),
% 7.30/7.51      inference('cnf', [status(esa)], [t102_enumset1])).
% 7.30/7.51  thf('50', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.30/7.51         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.30/7.51      inference('sup+', [status(thm)], ['48', '49'])).
% 7.30/7.51  thf('51', plain,
% 7.30/7.51      (![X44 : $i, X45 : $i, X46 : $i]:
% 7.30/7.51         ((k2_enumset1 @ X44 @ X44 @ X45 @ X46)
% 7.30/7.51           = (k1_enumset1 @ X44 @ X45 @ X46))),
% 7.30/7.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.30/7.51  thf('52', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.30/7.51         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.30/7.51      inference('sup+', [status(thm)], ['50', '51'])).
% 7.30/7.51  thf('53', plain,
% 7.30/7.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.30/7.51         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.30/7.51      inference('sup+', [status(thm)], ['48', '49'])).
% 7.30/7.51  thf('54', plain,
% 7.30/7.51      (![X69 : $i, X70 : $i, X71 : $i]:
% 7.30/7.51         ((k1_enumset1 @ X69 @ X71 @ X70) = (k1_enumset1 @ X69 @ X70 @ X71))),
% 7.30/7.51      inference('cnf', [status(esa)], [t98_enumset1])).
% 7.30/7.51  thf('55', plain,
% 7.30/7.51      (((k1_enumset1 @ sk_A @ sk_B @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 7.30/7.51      inference('demod', [status(thm)], ['27', '42', '47', '52', '53', '54'])).
% 7.30/7.51  thf(d1_enumset1, axiom,
% 7.30/7.51    (![A:$i,B:$i,C:$i,D:$i]:
% 7.30/7.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 7.30/7.51       ( ![E:$i]:
% 7.30/7.51         ( ( r2_hidden @ E @ D ) <=>
% 7.30/7.51           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 7.30/7.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 7.30/7.51  thf(zf_stmt_2, axiom,
% 7.30/7.51    (![E:$i,C:$i,B:$i,A:$i]:
% 7.30/7.51     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 7.30/7.51       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 7.30/7.51  thf(zf_stmt_3, axiom,
% 7.30/7.51    (![A:$i,B:$i,C:$i,D:$i]:
% 7.30/7.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 7.30/7.51       ( ![E:$i]:
% 7.30/7.51         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 7.30/7.51  thf('56', plain,
% 7.30/7.51      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 7.30/7.51         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 7.30/7.51          | (r2_hidden @ X18 @ X22)
% 7.30/7.51          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 7.30/7.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.30/7.51  thf('57', plain,
% 7.30/7.51      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 7.30/7.51         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 7.30/7.51          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 7.30/7.51      inference('simplify', [status(thm)], ['56'])).
% 7.30/7.51  thf('58', plain,
% 7.30/7.51      (![X0 : $i]:
% 7.30/7.51         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 7.30/7.51          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A))),
% 7.30/7.51      inference('sup+', [status(thm)], ['55', '57'])).
% 7.30/7.51  thf(d2_tarski, axiom,
% 7.30/7.51    (![A:$i,B:$i,C:$i]:
% 7.30/7.51     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 7.30/7.51       ( ![D:$i]:
% 7.30/7.51         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 7.30/7.51  thf('59', plain,
% 7.30/7.51      (![X25 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 7.30/7.51         (~ (r2_hidden @ X29 @ X27)
% 7.30/7.51          | ((X29) = (X28))
% 7.30/7.51          | ((X29) = (X25))
% 7.30/7.51          | ((X27) != (k2_tarski @ X28 @ X25)))),
% 7.30/7.51      inference('cnf', [status(esa)], [d2_tarski])).
% 7.30/7.51  thf('60', plain,
% 7.30/7.51      (![X25 : $i, X28 : $i, X29 : $i]:
% 7.30/7.51         (((X29) = (X25))
% 7.30/7.51          | ((X29) = (X28))
% 7.30/7.51          | ~ (r2_hidden @ X29 @ (k2_tarski @ X28 @ X25)))),
% 7.30/7.51      inference('simplify', [status(thm)], ['59'])).
% 7.30/7.51  thf('61', plain,
% 7.30/7.51      (![X0 : $i]:
% 7.30/7.51         ((zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A)
% 7.30/7.51          | ((X0) = (sk_B))
% 7.30/7.51          | ((X0) = (sk_C)))),
% 7.30/7.51      inference('sup-', [status(thm)], ['58', '60'])).
% 7.30/7.51  thf('62', plain,
% 7.30/7.51      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 7.30/7.51         (((X14) != (X13)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 7.30/7.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.30/7.51  thf('63', plain,
% 7.30/7.51      (![X13 : $i, X15 : $i, X16 : $i]:
% 7.30/7.51         ~ (zip_tseitin_0 @ X13 @ X15 @ X16 @ X13)),
% 7.30/7.51      inference('simplify', [status(thm)], ['62'])).
% 7.30/7.51  thf('64', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 7.30/7.51      inference('sup-', [status(thm)], ['61', '63'])).
% 7.30/7.51  thf('65', plain, (((sk_A) != (sk_B))),
% 7.30/7.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.51  thf('66', plain, (((sk_A) != (sk_C))),
% 7.30/7.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.51  thf('67', plain, ($false),
% 7.30/7.51      inference('simplify_reflect-', [status(thm)], ['64', '65', '66'])).
% 7.30/7.51  
% 7.30/7.51  % SZS output end Refutation
% 7.30/7.51  
% 7.30/7.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
