%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8WElTnJDs6

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:56 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 139 expanded)
%              Number of leaves         :   29 (  56 expanded)
%              Depth                    :   17
%              Number of atoms          : 1285 (1880 expanded)
%              Number of equality atoms :  104 ( 155 expanded)
%              Maximal formula depth    :   25 (  12 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

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

thf(zf_stmt_0,axiom,(
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

thf('0',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 )
      | ( X5 = X9 )
      | ( X5 = X10 )
      | ( X5 = X11 )
      | ( X5 = X12 )
      | ( X5 = X13 )
      | ( X5 = X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ B @ C ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k1_tarski @ A )
          = ( k2_tarski @ B @ C ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t8_zfmisc_1])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 )
      = ( k2_enumset1 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( k4_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 )
      = ( k3_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('6',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ( k5_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 )
      = ( k4_enumset1 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('7',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k6_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k1_tarski @ X37 ) @ ( k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('9',plain,(
    ! [X66: $i,X67: $i,X68: $i,X69: $i,X70: $i,X71: $i,X72: $i] :
      ( ( k6_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 )
      = ( k5_enumset1 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('10',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ( k5_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 )
      = ( k4_enumset1 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( k4_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 )
      = ( k3_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 )
      = ( k2_enumset1 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','18'])).

thf('20',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','21'])).

thf('23',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_enumset1 @ sk_B @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['1','22'])).

thf('24',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X45: $i] :
      ( ( k2_tarski @ X45 @ X45 )
      = ( k1_tarski @ X45 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('31',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 )
      = ( k2_enumset1 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('32',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( k4_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 )
      = ( k3_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k6_enumset1 @ X3 @ X2 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X66: $i,X67: $i,X68: $i,X69: $i,X70: $i,X71: $i,X72: $i] :
      ( ( k6_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 )
      = ( k5_enumset1 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('39',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k6_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k1_tarski @ X37 ) @ ( k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k6_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t127_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) ) ) )).

thf('41',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k7_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_tarski @ X28 ) @ ( k6_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t127_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k7_enumset1 @ X7 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i,J: $i] :
      ( ( J
        = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) )
    <=> ! [K: $i] :
          ( ( r2_hidden @ K @ J )
        <=> ~ ( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X15 @ X25 )
      | ( X25
       != ( k7_enumset1 @ X24 @ X23 @ X22 @ X21 @ X20 @ X19 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X15 @ ( k7_enumset1 @ X24 @ X23 @ X22 @ X21 @ X20 @ X19 @ X18 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 @ X7 ) ) ),
    inference('sup+',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X4: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X4 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( r2_hidden @ X0 @ ( k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','48'])).

thf('50',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['26','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('52',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('53',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 )
      = ( k2_enumset1 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('54',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( k4_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 )
      = ( k3_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k7_enumset1 @ X7 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ~ ( zip_tseitin_0 @ X26 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 )
      | ( X25
       != ( k7_enumset1 @ X24 @ X23 @ X22 @ X21 @ X20 @ X19 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 )
      | ~ ( r2_hidden @ X26 @ ( k7_enumset1 @ X24 @ X23 @ X22 @ X21 @ X20 @ X19 @ X18 @ X17 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 @ X7 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X5 @ X5 ) ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['52','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','63'])).

thf('65',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['50','64'])).

thf('66',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','65'])).

thf('67',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8WElTnJDs6
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:47:54 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.34  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.77/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.98  % Solved by: fo/fo7.sh
% 0.77/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.98  % done 476 iterations in 0.520s
% 0.77/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.98  % SZS output start Refutation
% 0.77/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.77/0.98  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.77/0.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.77/0.98                                               $i > $i > $i > $i > $o).
% 0.77/0.98  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.77/0.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/0.98  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.77/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.98  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.77/0.98  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.77/0.98  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.77/0.98                                           $i > $i).
% 0.77/0.98  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.77/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.98  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.77/0.98                                           $i > $i > $i).
% 0.77/0.98  thf(d7_enumset1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i,J:$i]:
% 0.77/0.98     ( ( ( J ) = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) ) <=>
% 0.77/0.98       ( ![K:$i]:
% 0.77/0.98         ( ( r2_hidden @ K @ J ) <=>
% 0.77/0.98           ( ~( ( ( K ) != ( I ) ) & ( ( K ) != ( H ) ) & ( ( K ) != ( G ) ) & 
% 0.77/0.98                ( ( K ) != ( F ) ) & ( ( K ) != ( E ) ) & ( ( K ) != ( D ) ) & 
% 0.77/0.98                ( ( K ) != ( C ) ) & ( ( K ) != ( B ) ) & ( ( K ) != ( A ) ) ) ) ) ) ))).
% 0.77/0.98  thf(zf_stmt_0, axiom,
% 0.77/0.98    (![K:$i,I:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.77/0.98     ( ( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.77/0.98       ( ( ( K ) != ( A ) ) & ( ( K ) != ( B ) ) & ( ( K ) != ( C ) ) & 
% 0.77/0.98         ( ( K ) != ( D ) ) & ( ( K ) != ( E ) ) & ( ( K ) != ( F ) ) & 
% 0.77/0.98         ( ( K ) != ( G ) ) & ( ( K ) != ( H ) ) & ( ( K ) != ( I ) ) ) ))).
% 0.77/0.98  thf('0', plain,
% 0.77/0.98      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.77/0.98         X12 : $i, X13 : $i, X14 : $i]:
% 0.77/0.98         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.77/0.98          | ((X5) = (X6))
% 0.77/0.98          | ((X5) = (X7))
% 0.77/0.98          | ((X5) = (X8))
% 0.77/0.98          | ((X5) = (X9))
% 0.77/0.98          | ((X5) = (X10))
% 0.77/0.98          | ((X5) = (X11))
% 0.77/0.98          | ((X5) = (X12))
% 0.77/0.98          | ((X5) = (X13))
% 0.77/0.98          | ((X5) = (X14)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(t8_zfmisc_1, conjecture,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( A ) = ( B ) ) ))).
% 0.77/0.98  thf(zf_stmt_1, negated_conjecture,
% 0.77/0.98    (~( ![A:$i,B:$i,C:$i]:
% 0.77/0.98        ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( A ) = ( B ) ) ) )),
% 0.77/0.98    inference('cnf.neg', [status(esa)], [t8_zfmisc_1])).
% 0.77/0.98  thf('1', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.77/0.98  thf(t70_enumset1, axiom,
% 0.77/0.98    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.77/0.98  thf('2', plain,
% 0.77/0.98      (![X46 : $i, X47 : $i]:
% 0.77/0.98         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 0.77/0.98      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.77/0.98  thf(t71_enumset1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.77/0.98  thf('3', plain,
% 0.77/0.98      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.77/0.98         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 0.77/0.98           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 0.77/0.98      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.77/0.98  thf(t72_enumset1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.98     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.77/0.98  thf('4', plain,
% 0.77/0.98      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.77/0.98         ((k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54)
% 0.77/0.98           = (k2_enumset1 @ X51 @ X52 @ X53 @ X54))),
% 0.77/0.98      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.77/0.98  thf(t73_enumset1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.77/0.98     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.77/0.98       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.77/0.98  thf('5', plain,
% 0.77/0.98      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.77/0.98         ((k4_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59)
% 0.77/0.98           = (k3_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59))),
% 0.77/0.98      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.77/0.98  thf(t74_enumset1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.77/0.98     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.77/0.98       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.77/0.98  thf('6', plain,
% 0.77/0.98      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 0.77/0.98         ((k5_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65)
% 0.77/0.98           = (k4_enumset1 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65))),
% 0.77/0.98      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.77/0.98  thf(t62_enumset1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.77/0.98     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.77/0.98       ( k2_xboole_0 @
% 0.77/0.98         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.77/0.98  thf('7', plain,
% 0.77/0.98      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, 
% 0.77/0.98         X44 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)
% 0.77/0.98           = (k2_xboole_0 @ (k1_tarski @ X37) @ 
% 0.77/0.98              (k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)))),
% 0.77/0.98      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.77/0.98  thf('8', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X6 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.77/0.98           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.77/0.98              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.77/0.98      inference('sup+', [status(thm)], ['6', '7'])).
% 0.77/0.98  thf(t75_enumset1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.77/0.98     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.77/0.98       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.77/0.98  thf('9', plain,
% 0.77/0.98      (![X66 : $i, X67 : $i, X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72)
% 0.77/0.98           = (k5_enumset1 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72))),
% 0.77/0.98      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.77/0.98  thf('10', plain,
% 0.77/0.98      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 0.77/0.98         ((k5_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65)
% 0.77/0.98           = (k4_enumset1 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65))),
% 0.77/0.98      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.77/0.98  thf('11', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.77/0.98           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.77/0.98      inference('sup+', [status(thm)], ['9', '10'])).
% 0.77/0.98  thf('12', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.77/0.98         ((k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.77/0.98           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.77/0.98           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.77/0.98      inference('sup+', [status(thm)], ['8', '11'])).
% 0.77/0.98  thf('13', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.77/0.98         ((k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.77/0.98           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.77/0.98           = (k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.77/0.98      inference('sup+', [status(thm)], ['5', '12'])).
% 0.77/0.98  thf('14', plain,
% 0.77/0.98      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.77/0.98         ((k4_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59)
% 0.77/0.98           = (k3_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59))),
% 0.77/0.98      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.77/0.98  thf('15', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.77/0.98         ((k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.77/0.98           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.77/0.98           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.77/0.98      inference('demod', [status(thm)], ['13', '14'])).
% 0.77/0.98  thf('16', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.77/0.98         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.77/0.98           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 0.77/0.98      inference('sup+', [status(thm)], ['4', '15'])).
% 0.77/0.98  thf('17', plain,
% 0.77/0.98      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.77/0.98         ((k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54)
% 0.77/0.98           = (k2_enumset1 @ X51 @ X52 @ X53 @ X54))),
% 0.77/0.98      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.77/0.98  thf('18', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.77/0.98         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.77/0.98           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.77/0.98      inference('demod', [status(thm)], ['16', '17'])).
% 0.77/0.98  thf('19', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.98         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.77/0.98           = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 0.77/0.98      inference('sup+', [status(thm)], ['3', '18'])).
% 0.77/0.98  thf('20', plain,
% 0.77/0.98      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.77/0.98         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 0.77/0.98           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 0.77/0.98      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.77/0.98  thf('21', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.98         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.77/0.98           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.77/0.98      inference('demod', [status(thm)], ['19', '20'])).
% 0.77/0.98  thf('22', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]:
% 0.77/0.98         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.77/0.98           = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.77/0.98      inference('sup+', [status(thm)], ['2', '21'])).
% 0.77/0.98  thf('23', plain,
% 0.77/0.98      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.77/0.98         = (k1_enumset1 @ sk_B @ sk_B @ sk_C))),
% 0.77/0.98      inference('sup+', [status(thm)], ['1', '22'])).
% 0.77/0.98  thf('24', plain,
% 0.77/0.98      (![X46 : $i, X47 : $i]:
% 0.77/0.98         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 0.77/0.98      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.77/0.98  thf('25', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.77/0.98  thf('26', plain,
% 0.77/0.98      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.77/0.98         = (k1_tarski @ sk_A))),
% 0.77/0.98      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.77/0.98  thf('27', plain,
% 0.77/0.98      (![X46 : $i, X47 : $i]:
% 0.77/0.98         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 0.77/0.98      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.77/0.98  thf(t69_enumset1, axiom,
% 0.77/0.98    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.77/0.98  thf('28', plain,
% 0.77/0.98      (![X45 : $i]: ((k2_tarski @ X45 @ X45) = (k1_tarski @ X45))),
% 0.77/0.98      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.77/0.98  thf('29', plain,
% 0.77/0.98      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.77/0.98      inference('sup+', [status(thm)], ['27', '28'])).
% 0.77/0.98  thf('30', plain,
% 0.77/0.98      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.77/0.98         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 0.77/0.98           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 0.77/0.98      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.77/0.98  thf('31', plain,
% 0.77/0.98      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.77/0.98         ((k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54)
% 0.77/0.98           = (k2_enumset1 @ X51 @ X52 @ X53 @ X54))),
% 0.77/0.98      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.77/0.98  thf('32', plain,
% 0.77/0.98      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.77/0.98         ((k4_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59)
% 0.77/0.98           = (k3_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59))),
% 0.77/0.98      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.77/0.98  thf('33', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X6 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.77/0.98           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.77/0.98              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.77/0.98      inference('sup+', [status(thm)], ['6', '7'])).
% 0.77/0.98  thf('34', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X5 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.77/0.98           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.77/0.98              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.77/0.98      inference('sup+', [status(thm)], ['32', '33'])).
% 0.77/0.98  thf('35', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X4 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.77/0.98           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.77/0.98              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.77/0.98      inference('sup+', [status(thm)], ['31', '34'])).
% 0.77/0.98  thf('36', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X3 @ X2 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 0.77/0.98           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.77/0.98      inference('sup+', [status(thm)], ['30', '35'])).
% 0.77/0.98  thf('37', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0)
% 0.77/0.98           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.77/0.98      inference('sup+', [status(thm)], ['29', '36'])).
% 0.77/0.98  thf('38', plain,
% 0.77/0.98      (![X66 : $i, X67 : $i, X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72)
% 0.77/0.98           = (k5_enumset1 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72))),
% 0.77/0.98      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.77/0.98  thf('39', plain,
% 0.77/0.98      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, 
% 0.77/0.98         X44 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)
% 0.77/0.98           = (k2_xboole_0 @ (k1_tarski @ X37) @ 
% 0.77/0.98              (k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)))),
% 0.77/0.98      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.77/0.98  thf('40', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.77/0.98           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.77/0.98              (k6_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.77/0.98      inference('sup+', [status(thm)], ['38', '39'])).
% 0.77/0.98  thf(t127_enumset1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.77/0.98     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.77/0.98       ( k2_xboole_0 @
% 0.77/0.98         ( k1_tarski @ A ) @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) ) ))).
% 0.77/0.98  thf('41', plain,
% 0.77/0.98      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, 
% 0.77/0.98         X35 : $i, X36 : $i]:
% 0.77/0.98         ((k7_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.77/0.98           = (k2_xboole_0 @ (k1_tarski @ X28) @ 
% 0.77/0.98              (k6_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)))),
% 0.77/0.98      inference('cnf', [status(esa)], [t127_enumset1])).
% 0.77/0.98  thf('42', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.77/0.98           = (k7_enumset1 @ X7 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.77/0.98      inference('demod', [status(thm)], ['40', '41'])).
% 0.77/0.98  thf(zf_stmt_2, type, zip_tseitin_0 :
% 0.77/0.98      $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.77/0.98  thf(zf_stmt_3, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i,J:$i]:
% 0.77/0.98     ( ( ( J ) = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) ) <=>
% 0.77/0.98       ( ![K:$i]:
% 0.77/0.98         ( ( r2_hidden @ K @ J ) <=>
% 0.77/0.98           ( ~( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.77/0.98  thf('43', plain,
% 0.77/0.98      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, 
% 0.77/0.98         X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.77/0.98         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ 
% 0.77/0.98           X23 @ X24)
% 0.77/0.98          | (r2_hidden @ X15 @ X25)
% 0.77/0.98          | ((X25)
% 0.77/0.98              != (k7_enumset1 @ X24 @ X23 @ X22 @ X21 @ X20 @ X19 @ X18 @ 
% 0.77/0.98                  X17 @ X16)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.77/0.98  thf('44', plain,
% 0.77/0.98      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, 
% 0.77/0.98         X22 : $i, X23 : $i, X24 : $i]:
% 0.77/0.98         ((r2_hidden @ X15 @ 
% 0.77/0.98           (k7_enumset1 @ X24 @ X23 @ X22 @ X21 @ X20 @ X19 @ X18 @ X17 @ X16))
% 0.77/0.98          | (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ 
% 0.77/0.98             X23 @ X24))),
% 0.77/0.98      inference('simplify', [status(thm)], ['43'])).
% 0.77/0.98  thf('45', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.77/0.98         X7 : $i, X8 : $i]:
% 0.77/0.98         ((r2_hidden @ X8 @ 
% 0.77/0.98           (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.77/0.98          | (zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 @ X7))),
% 0.77/0.98      inference('sup+', [status(thm)], ['42', '44'])).
% 0.77/0.98  thf('46', plain,
% 0.77/0.98      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, 
% 0.77/0.98         X11 : $i, X12 : $i, X13 : $i]:
% 0.77/0.98         (((X5) != (X4))
% 0.77/0.98          | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ 
% 0.77/0.98               X13 @ X4))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('47', plain,
% 0.77/0.98      (![X4 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.77/0.98         X12 : $i, X13 : $i]:
% 0.77/0.98         ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X4)),
% 0.77/0.98      inference('simplify', [status(thm)], ['46'])).
% 0.77/0.98  thf('48', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.77/0.98         (r2_hidden @ X0 @ 
% 0.77/0.98          (k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7))),
% 0.77/0.98      inference('sup-', [status(thm)], ['45', '47'])).
% 0.77/0.98  thf('49', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]:
% 0.77/0.98         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.77/0.98      inference('sup+', [status(thm)], ['37', '48'])).
% 0.77/0.98  thf('50', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.77/0.98      inference('sup+', [status(thm)], ['26', '49'])).
% 0.77/0.98  thf('51', plain,
% 0.77/0.98      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.77/0.98      inference('sup+', [status(thm)], ['27', '28'])).
% 0.77/0.98  thf('52', plain,
% 0.77/0.98      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.77/0.98         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 0.77/0.98           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 0.77/0.98      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.77/0.98  thf('53', plain,
% 0.77/0.98      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.77/0.98         ((k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54)
% 0.77/0.98           = (k2_enumset1 @ X51 @ X52 @ X53 @ X54))),
% 0.77/0.98      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.77/0.98  thf('54', plain,
% 0.77/0.98      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.77/0.98         ((k4_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59)
% 0.77/0.98           = (k3_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59))),
% 0.77/0.98      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.77/0.98  thf('55', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.77/0.98           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.77/0.98      inference('sup+', [status(thm)], ['9', '10'])).
% 0.77/0.98  thf('56', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.77/0.98         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.77/0.98           = (k7_enumset1 @ X7 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.77/0.98      inference('demod', [status(thm)], ['40', '41'])).
% 0.77/0.98  thf('57', plain,
% 0.77/0.98      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.77/0.98         X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.77/0.98         (~ (r2_hidden @ X26 @ X25)
% 0.77/0.98          | ~ (zip_tseitin_0 @ X26 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ 
% 0.77/0.98               X23 @ X24)
% 0.77/0.98          | ((X25)
% 0.77/0.98              != (k7_enumset1 @ X24 @ X23 @ X22 @ X21 @ X20 @ X19 @ X18 @ 
% 0.77/0.98                  X17 @ X16)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.77/0.98  thf('58', plain,
% 0.77/0.98      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.77/0.98         X23 : $i, X24 : $i, X26 : $i]:
% 0.77/0.98         (~ (zip_tseitin_0 @ X26 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ 
% 0.77/0.98             X23 @ X24)
% 0.77/0.98          | ~ (r2_hidden @ X26 @ 
% 0.77/0.98               (k7_enumset1 @ X24 @ X23 @ X22 @ X21 @ X20 @ X19 @ X18 @ X17 @ 
% 0.77/0.98                X16)))),
% 0.77/0.98      inference('simplify', [status(thm)], ['57'])).
% 0.77/0.98  thf('59', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.77/0.98         X7 : $i, X8 : $i]:
% 0.77/0.98         (~ (r2_hidden @ X8 @ 
% 0.77/0.98             (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.77/0.98          | ~ (zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 @ X7))),
% 0.77/0.98      inference('sup-', [status(thm)], ['56', '58'])).
% 0.77/0.98  thf('60', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.77/0.98         (~ (r2_hidden @ X6 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.77/0.98          | ~ (zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X5 @ X5))),
% 0.77/0.98      inference('sup-', [status(thm)], ['55', '59'])).
% 0.77/0.98  thf('61', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.77/0.98         (~ (r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.77/0.98          | ~ (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4 @ X4))),
% 0.77/0.98      inference('sup-', [status(thm)], ['54', '60'])).
% 0.77/0.98  thf('62', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.77/0.98         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.77/0.98          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3 @ X3))),
% 0.77/0.98      inference('sup-', [status(thm)], ['53', '61'])).
% 0.77/0.98  thf('63', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.77/0.98         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.77/0.98          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2))),
% 0.77/0.98      inference('sup-', [status(thm)], ['52', '62'])).
% 0.77/0.98  thf('64', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]:
% 0.77/0.98         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.77/0.98          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.77/0.98      inference('sup-', [status(thm)], ['51', '63'])).
% 0.77/0.98  thf('65', plain,
% 0.77/0.98      (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.77/0.98          sk_A @ sk_A @ sk_A)),
% 0.77/0.98      inference('sup-', [status(thm)], ['50', '64'])).
% 0.77/0.98  thf('66', plain,
% 0.77/0.98      ((((sk_B) = (sk_A))
% 0.77/0.98        | ((sk_B) = (sk_A))
% 0.77/0.98        | ((sk_B) = (sk_A))
% 0.77/0.98        | ((sk_B) = (sk_A))
% 0.77/0.98        | ((sk_B) = (sk_A))
% 0.77/0.98        | ((sk_B) = (sk_A))
% 0.77/0.98        | ((sk_B) = (sk_A))
% 0.77/0.98        | ((sk_B) = (sk_A))
% 0.77/0.98        | ((sk_B) = (sk_A)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['0', '65'])).
% 0.77/0.98  thf('67', plain, (((sk_B) = (sk_A))),
% 0.77/0.98      inference('simplify', [status(thm)], ['66'])).
% 0.77/0.98  thf('68', plain, (((sk_A) != (sk_B))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.77/0.98  thf('69', plain, ($false),
% 0.77/0.98      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 0.77/0.98  
% 0.77/0.98  % SZS output end Refutation
% 0.77/0.98  
% 0.77/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
