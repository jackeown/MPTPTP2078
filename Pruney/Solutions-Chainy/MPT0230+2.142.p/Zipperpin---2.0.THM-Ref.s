%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kmRLW4rZeS

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:27 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 117 expanded)
%              Number of leaves         :   39 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          : 1106 (1441 expanded)
%              Number of equality atoms :   96 ( 127 expanded)
%              Maximal formula depth    :   25 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 )
      | ( X9 = X13 )
      | ( X9 = X14 )
      | ( X9 = X15 )
      | ( X9 = X16 )
      | ( X9 = X17 )
      | ( X9 = X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('11',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k1_enumset1 @ X59 @ X59 @ X60 )
      = ( k2_tarski @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X58: $i] :
      ( ( k2_tarski @ X58 @ X58 )
      = ( k1_tarski @ X58 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('15',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( k2_enumset1 @ X61 @ X61 @ X62 @ X63 )
      = ( k1_enumset1 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('16',plain,(
    ! [X64: $i,X65: $i,X66: $i,X67: $i] :
      ( ( k3_enumset1 @ X64 @ X64 @ X65 @ X66 @ X67 )
      = ( k2_enumset1 @ X64 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('17',plain,(
    ! [X68: $i,X69: $i,X70: $i,X71: $i,X72: $i] :
      ( ( k4_enumset1 @ X68 @ X68 @ X69 @ X70 @ X71 @ X72 )
      = ( k3_enumset1 @ X68 @ X69 @ X70 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t63_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('18',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k6_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 )
      = ( k2_xboole_0 @ ( k2_tarski @ X50 @ X51 ) @ ( k4_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t63_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X4 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('21',plain,(
    ! [X73: $i,X74: $i,X75: $i,X76: $i,X77: $i,X78: $i] :
      ( ( k5_enumset1 @ X73 @ X73 @ X74 @ X75 @ X76 @ X77 @ X78 )
      = ( k4_enumset1 @ X73 @ X74 @ X75 @ X76 @ X77 @ X78 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t128_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k5_enumset1 @ C @ D @ E @ F @ G @ H @ I ) ) ) )).

thf('22',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k7_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_xboole_0 @ ( k2_tarski @ X41 @ X42 ) @ ( k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t128_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X7 @ X6 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k6_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 )
      = ( k2_xboole_0 @ ( k2_tarski @ X50 @ X51 ) @ ( k4_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t63_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X7 @ X6 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i,J: $i] :
      ( ( J
        = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) )
    <=> ! [K: $i] :
          ( ( r2_hidden @ K @ J )
        <=> ~ ( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X19 @ X29 )
      | ( X29
       != ( k7_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24 @ X23 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X19 @ ( k7_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24 @ X23 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X6 @ X7 ) ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X9 != X16 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X8: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X8 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( r2_hidden @ X2 @ ( k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X3 @ ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X2 @ ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','33'])).

thf('35',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['11','34'])).

thf('36',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k1_enumset1 @ X59 @ X59 @ X60 )
      = ( k2_tarski @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('37',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( k2_enumset1 @ X61 @ X61 @ X62 @ X63 )
      = ( k1_enumset1 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('38',plain,(
    ! [X64: $i,X65: $i,X66: $i,X67: $i] :
      ( ( k3_enumset1 @ X64 @ X64 @ X65 @ X66 @ X67 )
      = ( k2_enumset1 @ X64 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('39',plain,(
    ! [X79: $i,X80: $i,X81: $i,X82: $i,X83: $i,X84: $i,X85: $i] :
      ( ( k6_enumset1 @ X79 @ X79 @ X80 @ X81 @ X82 @ X83 @ X84 @ X85 )
      = ( k5_enumset1 @ X79 @ X80 @ X81 @ X82 @ X83 @ X84 @ X85 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('40',plain,(
    ! [X73: $i,X74: $i,X75: $i,X76: $i,X77: $i,X78: $i] :
      ( ( k5_enumset1 @ X73 @ X73 @ X74 @ X75 @ X76 @ X77 @ X78 )
      = ( k4_enumset1 @ X73 @ X74 @ X75 @ X76 @ X77 @ X78 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('41',plain,(
    ! [X68: $i,X69: $i,X70: $i,X71: $i,X72: $i] :
      ( ( k4_enumset1 @ X68 @ X68 @ X69 @ X70 @ X71 @ X72 )
      = ( k3_enumset1 @ X68 @ X69 @ X70 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X7 @ X6 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      | ( X29
       != ( k7_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24 @ X23 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k7_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24 @ X23 @ X22 @ X21 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X6 @ X7 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','50'])).

thf('52',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['35','51'])).

thf('53',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['0','52'])).

thf('54',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kmRLW4rZeS
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:32:18 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.68/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.92  % Solved by: fo/fo7.sh
% 0.68/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.92  % done 836 iterations in 0.476s
% 0.68/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.92  % SZS output start Refutation
% 0.68/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.92  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.68/0.92  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.68/0.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.92  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.68/0.92  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.68/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.92  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.68/0.92                                           $i > $i).
% 0.68/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.92  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.68/0.92                                           $i > $i > $i).
% 0.68/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.92  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.68/0.92  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.68/0.92                                               $i > $i > $i > $i > $o).
% 0.68/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.92  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.68/0.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.92  thf(d7_enumset1, axiom,
% 0.68/0.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i,J:$i]:
% 0.68/0.92     ( ( ( J ) = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) ) <=>
% 0.68/0.92       ( ![K:$i]:
% 0.68/0.92         ( ( r2_hidden @ K @ J ) <=>
% 0.68/0.92           ( ~( ( ( K ) != ( I ) ) & ( ( K ) != ( H ) ) & ( ( K ) != ( G ) ) & 
% 0.68/0.92                ( ( K ) != ( F ) ) & ( ( K ) != ( E ) ) & ( ( K ) != ( D ) ) & 
% 0.68/0.92                ( ( K ) != ( C ) ) & ( ( K ) != ( B ) ) & ( ( K ) != ( A ) ) ) ) ) ) ))).
% 0.68/0.92  thf(zf_stmt_0, axiom,
% 0.68/0.92    (![K:$i,I:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.68/0.92     ( ( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.68/0.92       ( ( ( K ) != ( A ) ) & ( ( K ) != ( B ) ) & ( ( K ) != ( C ) ) & 
% 0.68/0.92         ( ( K ) != ( D ) ) & ( ( K ) != ( E ) ) & ( ( K ) != ( F ) ) & 
% 0.68/0.92         ( ( K ) != ( G ) ) & ( ( K ) != ( H ) ) & ( ( K ) != ( I ) ) ) ))).
% 0.68/0.92  thf('0', plain,
% 0.68/0.92      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, 
% 0.68/0.92         X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.92         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ 
% 0.68/0.92           X17 @ X18)
% 0.68/0.92          | ((X9) = (X10))
% 0.68/0.92          | ((X9) = (X11))
% 0.68/0.92          | ((X9) = (X12))
% 0.68/0.92          | ((X9) = (X13))
% 0.68/0.92          | ((X9) = (X14))
% 0.68/0.92          | ((X9) = (X15))
% 0.68/0.92          | ((X9) = (X16))
% 0.68/0.92          | ((X9) = (X17))
% 0.68/0.92          | ((X9) = (X18)))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf(t25_zfmisc_1, conjecture,
% 0.68/0.92    (![A:$i,B:$i,C:$i]:
% 0.68/0.92     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.68/0.92          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.68/0.92  thf(zf_stmt_1, negated_conjecture,
% 0.68/0.92    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.92        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.68/0.92             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.68/0.92    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.68/0.92  thf('1', plain,
% 0.68/0.92      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.68/0.92  thf(t28_xboole_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.68/0.92  thf('2', plain,
% 0.68/0.92      (![X2 : $i, X3 : $i]:
% 0.68/0.92         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.68/0.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.68/0.92  thf('3', plain,
% 0.68/0.92      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.68/0.92         = (k1_tarski @ sk_A))),
% 0.68/0.92      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.92  thf(t100_xboole_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.68/0.92  thf('4', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k4_xboole_0 @ X0 @ X1)
% 0.68/0.92           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.68/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.92  thf('5', plain,
% 0.68/0.92      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.68/0.92         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['3', '4'])).
% 0.68/0.92  thf(t92_xboole_1, axiom,
% 0.68/0.92    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.68/0.92  thf('6', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.68/0.92      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.68/0.92  thf('7', plain,
% 0.68/0.92      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.68/0.92         = (k1_xboole_0))),
% 0.68/0.92      inference('demod', [status(thm)], ['5', '6'])).
% 0.68/0.92  thf(t98_xboole_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.68/0.92  thf('8', plain,
% 0.68/0.92      (![X6 : $i, X7 : $i]:
% 0.68/0.92         ((k2_xboole_0 @ X6 @ X7)
% 0.68/0.92           = (k5_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6)))),
% 0.68/0.92      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.68/0.92  thf('9', plain,
% 0.68/0.92      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.68/0.92         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.68/0.92      inference('sup+', [status(thm)], ['7', '8'])).
% 0.68/0.92  thf(t5_boole, axiom,
% 0.68/0.92    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.68/0.92  thf('10', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.68/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.68/0.92  thf('11', plain,
% 0.68/0.92      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.68/0.92         = (k2_tarski @ sk_B @ sk_C))),
% 0.68/0.92      inference('demod', [status(thm)], ['9', '10'])).
% 0.68/0.92  thf(t70_enumset1, axiom,
% 0.68/0.92    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.68/0.92  thf('12', plain,
% 0.68/0.92      (![X59 : $i, X60 : $i]:
% 0.68/0.92         ((k1_enumset1 @ X59 @ X59 @ X60) = (k2_tarski @ X59 @ X60))),
% 0.68/0.92      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.68/0.92  thf(t69_enumset1, axiom,
% 0.68/0.92    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.68/0.92  thf('13', plain,
% 0.68/0.92      (![X58 : $i]: ((k2_tarski @ X58 @ X58) = (k1_tarski @ X58))),
% 0.68/0.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.68/0.92  thf('14', plain,
% 0.68/0.92      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.68/0.92      inference('sup+', [status(thm)], ['12', '13'])).
% 0.68/0.92  thf(t71_enumset1, axiom,
% 0.68/0.92    (![A:$i,B:$i,C:$i]:
% 0.68/0.92     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.68/0.92  thf('15', plain,
% 0.68/0.92      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.68/0.92         ((k2_enumset1 @ X61 @ X61 @ X62 @ X63)
% 0.68/0.92           = (k1_enumset1 @ X61 @ X62 @ X63))),
% 0.68/0.92      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.68/0.92  thf(t72_enumset1, axiom,
% 0.68/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.92     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.68/0.92  thf('16', plain,
% 0.68/0.92      (![X64 : $i, X65 : $i, X66 : $i, X67 : $i]:
% 0.68/0.92         ((k3_enumset1 @ X64 @ X64 @ X65 @ X66 @ X67)
% 0.68/0.92           = (k2_enumset1 @ X64 @ X65 @ X66 @ X67))),
% 0.68/0.92      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.68/0.92  thf(t73_enumset1, axiom,
% 0.68/0.92    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.68/0.92     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.68/0.92       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.68/0.92  thf('17', plain,
% 0.68/0.92      (![X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i]:
% 0.68/0.92         ((k4_enumset1 @ X68 @ X68 @ X69 @ X70 @ X71 @ X72)
% 0.68/0.92           = (k3_enumset1 @ X68 @ X69 @ X70 @ X71 @ X72))),
% 0.68/0.92      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.68/0.92  thf(t63_enumset1, axiom,
% 0.68/0.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.68/0.92     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.68/0.92       ( k2_xboole_0 @
% 0.68/0.92         ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.68/0.92  thf('18', plain,
% 0.68/0.92      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, 
% 0.68/0.92         X57 : $i]:
% 0.68/0.92         ((k6_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57)
% 0.68/0.92           = (k2_xboole_0 @ (k2_tarski @ X50 @ X51) @ 
% 0.68/0.92              (k4_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57)))),
% 0.68/0.92      inference('cnf', [status(esa)], [t63_enumset1])).
% 0.68/0.92  thf('19', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.68/0.92         ((k6_enumset1 @ X6 @ X5 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.68/0.92           = (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.68/0.92              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['17', '18'])).
% 0.68/0.92  thf('20', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.68/0.92         ((k6_enumset1 @ X5 @ X4 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.68/0.92           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.68/0.92              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['16', '19'])).
% 0.68/0.92  thf(t74_enumset1, axiom,
% 0.68/0.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.68/0.92     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.68/0.92       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.68/0.92  thf('21', plain,
% 0.68/0.92      (![X73 : $i, X74 : $i, X75 : $i, X76 : $i, X77 : $i, X78 : $i]:
% 0.68/0.92         ((k5_enumset1 @ X73 @ X73 @ X74 @ X75 @ X76 @ X77 @ X78)
% 0.68/0.92           = (k4_enumset1 @ X73 @ X74 @ X75 @ X76 @ X77 @ X78))),
% 0.68/0.92      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.68/0.92  thf(t128_enumset1, axiom,
% 0.68/0.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.68/0.92     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.68/0.92       ( k2_xboole_0 @
% 0.68/0.92         ( k2_tarski @ A @ B ) @ ( k5_enumset1 @ C @ D @ E @ F @ G @ H @ I ) ) ))).
% 0.68/0.92  thf('22', plain,
% 0.68/0.92      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, 
% 0.68/0.92         X48 : $i, X49 : $i]:
% 0.68/0.92         ((k7_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 0.68/0.92           = (k2_xboole_0 @ (k2_tarski @ X41 @ X42) @ 
% 0.68/0.92              (k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)))),
% 0.68/0.92      inference('cnf', [status(esa)], [t128_enumset1])).
% 0.68/0.92  thf('23', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.68/0.92         ((k7_enumset1 @ X7 @ X6 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.68/0.92           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.68/0.92              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['21', '22'])).
% 0.68/0.92  thf('24', plain,
% 0.68/0.92      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, 
% 0.68/0.92         X57 : $i]:
% 0.68/0.92         ((k6_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57)
% 0.68/0.92           = (k2_xboole_0 @ (k2_tarski @ X50 @ X51) @ 
% 0.68/0.92              (k4_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57)))),
% 0.68/0.92      inference('cnf', [status(esa)], [t63_enumset1])).
% 0.68/0.92  thf('25', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.68/0.92         ((k7_enumset1 @ X7 @ X6 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.68/0.92           = (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['23', '24'])).
% 0.68/0.92  thf(zf_stmt_2, type, zip_tseitin_0 :
% 0.68/0.92      $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.68/0.92  thf(zf_stmt_3, axiom,
% 0.68/0.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i,J:$i]:
% 0.68/0.92     ( ( ( J ) = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) ) <=>
% 0.68/0.92       ( ![K:$i]:
% 0.68/0.92         ( ( r2_hidden @ K @ J ) <=>
% 0.68/0.92           ( ~( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.68/0.92  thf('26', plain,
% 0.68/0.92      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.68/0.92         X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.68/0.92         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ 
% 0.68/0.92           X27 @ X28)
% 0.68/0.92          | (r2_hidden @ X19 @ X29)
% 0.68/0.92          | ((X29)
% 0.68/0.92              != (k7_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24 @ X23 @ X22 @ 
% 0.68/0.92                  X21 @ X20)))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.92  thf('27', plain,
% 0.68/0.92      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.68/0.92         X26 : $i, X27 : $i, X28 : $i]:
% 0.68/0.92         ((r2_hidden @ X19 @ 
% 0.68/0.92           (k7_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24 @ X23 @ X22 @ X21 @ X20))
% 0.68/0.92          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ 
% 0.68/0.92             X27 @ X28))),
% 0.68/0.92      inference('simplify', [status(thm)], ['26'])).
% 0.68/0.92  thf('28', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.68/0.92         X7 : $i, X8 : $i]:
% 0.68/0.92         ((r2_hidden @ X8 @ 
% 0.68/0.92           (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.68/0.92          | (zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X6 @ X7))),
% 0.68/0.92      inference('sup+', [status(thm)], ['25', '27'])).
% 0.68/0.92  thf('29', plain,
% 0.68/0.92      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 0.68/0.92         X15 : $i, X16 : $i, X17 : $i]:
% 0.68/0.92         (((X9) != (X16))
% 0.68/0.92          | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ 
% 0.68/0.92               X17 @ X8))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('30', plain,
% 0.68/0.92      (![X8 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, 
% 0.68/0.92         X16 : $i, X17 : $i]:
% 0.68/0.92         ~ (zip_tseitin_0 @ X16 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ 
% 0.68/0.92            X17 @ X8)),
% 0.68/0.92      inference('simplify', [status(thm)], ['29'])).
% 0.68/0.92  thf('31', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.68/0.92         (r2_hidden @ X2 @ 
% 0.68/0.92          (k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7))),
% 0.68/0.92      inference('sup-', [status(thm)], ['28', '30'])).
% 0.68/0.92  thf('32', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.68/0.92         (r2_hidden @ X3 @ 
% 0.68/0.92          (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.68/0.92           (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['20', '31'])).
% 0.68/0.92  thf('33', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.68/0.92         (r2_hidden @ X2 @ 
% 0.68/0.92          (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['15', '32'])).
% 0.68/0.92  thf('34', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         (r2_hidden @ X0 @ 
% 0.68/0.92          (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['14', '33'])).
% 0.68/0.92  thf('35', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.68/0.92      inference('sup+', [status(thm)], ['11', '34'])).
% 0.68/0.92  thf('36', plain,
% 0.68/0.92      (![X59 : $i, X60 : $i]:
% 0.68/0.92         ((k1_enumset1 @ X59 @ X59 @ X60) = (k2_tarski @ X59 @ X60))),
% 0.68/0.92      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.68/0.92  thf('37', plain,
% 0.68/0.92      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.68/0.92         ((k2_enumset1 @ X61 @ X61 @ X62 @ X63)
% 0.68/0.92           = (k1_enumset1 @ X61 @ X62 @ X63))),
% 0.68/0.92      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.68/0.92  thf('38', plain,
% 0.68/0.92      (![X64 : $i, X65 : $i, X66 : $i, X67 : $i]:
% 0.68/0.92         ((k3_enumset1 @ X64 @ X64 @ X65 @ X66 @ X67)
% 0.68/0.92           = (k2_enumset1 @ X64 @ X65 @ X66 @ X67))),
% 0.68/0.92      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.68/0.92  thf(t75_enumset1, axiom,
% 0.68/0.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.68/0.92     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.68/0.92       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.68/0.92  thf('39', plain,
% 0.68/0.92      (![X79 : $i, X80 : $i, X81 : $i, X82 : $i, X83 : $i, X84 : $i, X85 : $i]:
% 0.68/0.92         ((k6_enumset1 @ X79 @ X79 @ X80 @ X81 @ X82 @ X83 @ X84 @ X85)
% 0.68/0.92           = (k5_enumset1 @ X79 @ X80 @ X81 @ X82 @ X83 @ X84 @ X85))),
% 0.68/0.92      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.68/0.92  thf('40', plain,
% 0.68/0.92      (![X73 : $i, X74 : $i, X75 : $i, X76 : $i, X77 : $i, X78 : $i]:
% 0.68/0.92         ((k5_enumset1 @ X73 @ X73 @ X74 @ X75 @ X76 @ X77 @ X78)
% 0.68/0.92           = (k4_enumset1 @ X73 @ X74 @ X75 @ X76 @ X77 @ X78))),
% 0.68/0.92      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.68/0.92  thf('41', plain,
% 0.68/0.92      (![X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i]:
% 0.68/0.92         ((k4_enumset1 @ X68 @ X68 @ X69 @ X70 @ X71 @ X72)
% 0.68/0.92           = (k3_enumset1 @ X68 @ X69 @ X70 @ X71 @ X72))),
% 0.68/0.92      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.68/0.92  thf('42', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.68/0.92         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.68/0.92           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.68/0.92      inference('sup+', [status(thm)], ['40', '41'])).
% 0.68/0.92  thf('43', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.68/0.92         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.68/0.92           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.68/0.92      inference('sup+', [status(thm)], ['39', '42'])).
% 0.68/0.92  thf('44', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.68/0.92         ((k7_enumset1 @ X7 @ X6 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.68/0.92           = (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['23', '24'])).
% 0.68/0.92  thf('45', plain,
% 0.68/0.92      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, 
% 0.68/0.92         X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.68/0.92         (~ (r2_hidden @ X30 @ X29)
% 0.68/0.92          | ~ (zip_tseitin_0 @ X30 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ 
% 0.68/0.92               X27 @ X28)
% 0.68/0.92          | ((X29)
% 0.68/0.92              != (k7_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24 @ X23 @ X22 @ 
% 0.68/0.92                  X21 @ X20)))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.92  thf('46', plain,
% 0.68/0.92      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, 
% 0.68/0.92         X27 : $i, X28 : $i, X30 : $i]:
% 0.68/0.92         (~ (zip_tseitin_0 @ X30 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ 
% 0.68/0.92             X27 @ X28)
% 0.68/0.92          | ~ (r2_hidden @ X30 @ 
% 0.68/0.92               (k7_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24 @ X23 @ X22 @ X21 @ 
% 0.68/0.92                X20)))),
% 0.68/0.92      inference('simplify', [status(thm)], ['45'])).
% 0.68/0.92  thf('47', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.68/0.92         X7 : $i, X8 : $i]:
% 0.68/0.92         (~ (r2_hidden @ X8 @ 
% 0.68/0.92             (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.68/0.92          | ~ (zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X6 @ X7))),
% 0.68/0.92      inference('sup-', [status(thm)], ['44', '46'])).
% 0.68/0.92  thf('48', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.68/0.92         (~ (r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.68/0.92          | ~ (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4 @ X4))),
% 0.68/0.92      inference('sup-', [status(thm)], ['43', '47'])).
% 0.68/0.92  thf('49', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.68/0.92         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.68/0.92          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3 @ X3))),
% 0.68/0.92      inference('sup-', [status(thm)], ['38', '48'])).
% 0.68/0.92  thf('50', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.92         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.68/0.92          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2))),
% 0.68/0.92      inference('sup-', [status(thm)], ['37', '49'])).
% 0.68/0.92  thf('51', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.68/0.92          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1))),
% 0.68/0.92      inference('sup-', [status(thm)], ['36', '50'])).
% 0.68/0.92  thf('52', plain,
% 0.68/0.92      (~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ 
% 0.68/0.92          sk_B @ sk_B @ sk_B)),
% 0.68/0.92      inference('sup-', [status(thm)], ['35', '51'])).
% 0.68/0.92  thf('53', plain,
% 0.68/0.92      ((((sk_A) = (sk_B))
% 0.68/0.92        | ((sk_A) = (sk_B))
% 0.68/0.92        | ((sk_A) = (sk_B))
% 0.68/0.92        | ((sk_A) = (sk_B))
% 0.68/0.92        | ((sk_A) = (sk_B))
% 0.68/0.92        | ((sk_A) = (sk_B))
% 0.68/0.92        | ((sk_A) = (sk_B))
% 0.68/0.92        | ((sk_A) = (sk_B))
% 0.68/0.92        | ((sk_A) = (sk_C)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['0', '52'])).
% 0.68/0.92  thf('54', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.68/0.92      inference('simplify', [status(thm)], ['53'])).
% 0.68/0.92  thf('55', plain, (((sk_A) != (sk_B))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.68/0.92  thf('56', plain, (((sk_A) != (sk_C))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.68/0.92  thf('57', plain, ($false),
% 0.68/0.92      inference('simplify_reflect-', [status(thm)], ['54', '55', '56'])).
% 0.68/0.92  
% 0.68/0.92  % SZS output end Refutation
% 0.68/0.92  
% 0.76/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
