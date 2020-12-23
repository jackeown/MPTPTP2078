%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.awyj2YfxNy

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:54 EST 2020

% Result     : Theorem 6.55s
% Output     : Refutation 6.55s
% Verified   : 
% Statistics : Number of formulae       :   79 (  82 expanded)
%              Number of leaves         :   37 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  755 ( 785 expanded)
%              Number of equality atoms :   53 (  54 expanded)
%              Maximal formula depth    :   25 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_B )
    | ( r2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k1_enumset1 @ X60 @ X60 @ X61 )
      = ( k2_tarski @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('5',plain,(
    ! [X80: $i,X81: $i,X82: $i,X83: $i,X84: $i,X85: $i,X86: $i] :
      ( ( k6_enumset1 @ X80 @ X80 @ X81 @ X82 @ X83 @ X84 @ X85 @ X86 )
      = ( k5_enumset1 @ X80 @ X81 @ X82 @ X83 @ X84 @ X85 @ X86 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('6',plain,(
    ! [X74: $i,X75: $i,X76: $i,X77: $i,X78: $i,X79: $i] :
      ( ( k5_enumset1 @ X74 @ X74 @ X75 @ X76 @ X77 @ X78 @ X79 )
      = ( k4_enumset1 @ X74 @ X75 @ X76 @ X77 @ X78 @ X79 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('8',plain,(
    ! [X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ( k3_enumset1 @ X65 @ X65 @ X66 @ X67 @ X68 )
      = ( k2_enumset1 @ X65 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('9',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( k2_enumset1 @ X62 @ X62 @ X63 @ X64 )
      = ( k1_enumset1 @ X62 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('11',plain,(
    ! [X69: $i,X70: $i,X71: $i,X72: $i,X73: $i] :
      ( ( k4_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72 @ X73 )
      = ( k3_enumset1 @ X69 @ X70 @ X71 @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ( k3_enumset1 @ X65 @ X65 @ X66 @ X67 @ X68 )
      = ( k2_enumset1 @ X65 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('15',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k6_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X42 @ X43 @ X44 @ X45 ) @ ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t131_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_enumset1 @ F @ G @ H @ I ) ) ) )).

thf('17',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( k7_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 ) @ ( k2_enumset1 @ X55 @ X56 @ X57 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t131_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 )
      = ( k7_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

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

thf('19',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 )
      | ( r2_hidden @ X29 @ X39 )
      | ( X39
       != ( k7_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X29 @ ( k7_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32 @ X31 @ X30 ) )
      | ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X7 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X19 != X20 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    ! [X18: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ~ ( zip_tseitin_0 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X18 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( r2_hidden @ X7 @ ( k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','25'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('27',plain,(
    ! [X87: $i,X88: $i] :
      ( ( r1_tarski @ X87 @ ( k3_tarski @ X88 ) )
      | ~ ( r2_hidden @ X87 @ X88 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X89: $i,X90: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X89 @ X90 ) )
      = ( k2_xboole_0 @ X89 @ X90 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r2_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['3','32'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('35',plain,(
    ! [X59: $i] :
      ( ( k2_tarski @ X59 @ X59 )
      = ( k1_tarski @ X59 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X91: $i,X92: $i,X93: $i] :
      ( ( r2_hidden @ X91 @ X92 )
      | ~ ( r1_tarski @ ( k2_tarski @ X91 @ X93 ) @ X92 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.awyj2YfxNy
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.55/6.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.55/6.76  % Solved by: fo/fo7.sh
% 6.55/6.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.55/6.76  % done 7701 iterations in 6.317s
% 6.55/6.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.55/6.76  % SZS output start Refutation
% 6.55/6.76  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 6.55/6.76  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 6.55/6.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.55/6.76  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 6.55/6.76  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 6.55/6.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.55/6.76  thf(sk_B_type, type, sk_B: $i).
% 6.55/6.76  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 6.55/6.76                                           $i > $i > $i).
% 6.55/6.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.55/6.76  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 6.55/6.76  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 6.55/6.76  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 6.55/6.76                                           $i > $i).
% 6.55/6.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.55/6.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 6.55/6.76                                               $i > $i > $i > $i > $o).
% 6.55/6.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.55/6.76  thf(sk_A_type, type, sk_A: $i).
% 6.55/6.76  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 6.55/6.76  thf(t45_zfmisc_1, conjecture,
% 6.55/6.76    (![A:$i,B:$i]:
% 6.55/6.76     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 6.55/6.76       ( r2_hidden @ A @ B ) ))).
% 6.55/6.76  thf(zf_stmt_0, negated_conjecture,
% 6.55/6.76    (~( ![A:$i,B:$i]:
% 6.55/6.76        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 6.55/6.76          ( r2_hidden @ A @ B ) ) )),
% 6.55/6.76    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 6.55/6.76  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 6.55/6.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.55/6.76  thf('1', plain,
% 6.55/6.76      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 6.55/6.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.55/6.77  thf(d8_xboole_0, axiom,
% 6.55/6.77    (![A:$i,B:$i]:
% 6.55/6.77     ( ( r2_xboole_0 @ A @ B ) <=>
% 6.55/6.77       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 6.55/6.77  thf('2', plain,
% 6.55/6.77      (![X2 : $i, X4 : $i]:
% 6.55/6.77         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 6.55/6.77      inference('cnf', [status(esa)], [d8_xboole_0])).
% 6.55/6.77  thf('3', plain,
% 6.55/6.77      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))
% 6.55/6.77        | (r2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B))),
% 6.55/6.77      inference('sup-', [status(thm)], ['1', '2'])).
% 6.55/6.77  thf(t70_enumset1, axiom,
% 6.55/6.77    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 6.55/6.77  thf('4', plain,
% 6.55/6.77      (![X60 : $i, X61 : $i]:
% 6.55/6.77         ((k1_enumset1 @ X60 @ X60 @ X61) = (k2_tarski @ X60 @ X61))),
% 6.55/6.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 6.55/6.77  thf(t75_enumset1, axiom,
% 6.55/6.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 6.55/6.77     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 6.55/6.77       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 6.55/6.77  thf('5', plain,
% 6.55/6.77      (![X80 : $i, X81 : $i, X82 : $i, X83 : $i, X84 : $i, X85 : $i, X86 : $i]:
% 6.55/6.77         ((k6_enumset1 @ X80 @ X80 @ X81 @ X82 @ X83 @ X84 @ X85 @ X86)
% 6.55/6.77           = (k5_enumset1 @ X80 @ X81 @ X82 @ X83 @ X84 @ X85 @ X86))),
% 6.55/6.77      inference('cnf', [status(esa)], [t75_enumset1])).
% 6.55/6.77  thf(t74_enumset1, axiom,
% 6.55/6.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.55/6.77     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 6.55/6.77       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 6.55/6.77  thf('6', plain,
% 6.55/6.77      (![X74 : $i, X75 : $i, X76 : $i, X77 : $i, X78 : $i, X79 : $i]:
% 6.55/6.77         ((k5_enumset1 @ X74 @ X74 @ X75 @ X76 @ X77 @ X78 @ X79)
% 6.55/6.77           = (k4_enumset1 @ X74 @ X75 @ X76 @ X77 @ X78 @ X79))),
% 6.55/6.77      inference('cnf', [status(esa)], [t74_enumset1])).
% 6.55/6.77  thf('7', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 6.55/6.77         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 6.55/6.77           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 6.55/6.77      inference('sup+', [status(thm)], ['5', '6'])).
% 6.55/6.77  thf(t72_enumset1, axiom,
% 6.55/6.77    (![A:$i,B:$i,C:$i,D:$i]:
% 6.55/6.77     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 6.55/6.77  thf('8', plain,
% 6.55/6.77      (![X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 6.55/6.77         ((k3_enumset1 @ X65 @ X65 @ X66 @ X67 @ X68)
% 6.55/6.77           = (k2_enumset1 @ X65 @ X66 @ X67 @ X68))),
% 6.55/6.77      inference('cnf', [status(esa)], [t72_enumset1])).
% 6.55/6.77  thf(t71_enumset1, axiom,
% 6.55/6.77    (![A:$i,B:$i,C:$i]:
% 6.55/6.77     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 6.55/6.77  thf('9', plain,
% 6.55/6.77      (![X62 : $i, X63 : $i, X64 : $i]:
% 6.55/6.77         ((k2_enumset1 @ X62 @ X62 @ X63 @ X64)
% 6.55/6.77           = (k1_enumset1 @ X62 @ X63 @ X64))),
% 6.55/6.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.55/6.77  thf('10', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.55/6.77         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.55/6.77      inference('sup+', [status(thm)], ['8', '9'])).
% 6.55/6.77  thf(t73_enumset1, axiom,
% 6.55/6.77    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.55/6.77     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 6.55/6.77       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 6.55/6.77  thf('11', plain,
% 6.55/6.77      (![X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i]:
% 6.55/6.77         ((k4_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72 @ X73)
% 6.55/6.77           = (k3_enumset1 @ X69 @ X70 @ X71 @ X72 @ X73))),
% 6.55/6.77      inference('cnf', [status(esa)], [t73_enumset1])).
% 6.55/6.77  thf('12', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.55/6.77         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 6.55/6.77           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.55/6.77      inference('sup+', [status(thm)], ['10', '11'])).
% 6.55/6.77  thf('13', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.55/6.77         ((k6_enumset1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 6.55/6.77           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.55/6.77      inference('sup+', [status(thm)], ['7', '12'])).
% 6.55/6.77  thf('14', plain,
% 6.55/6.77      (![X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 6.55/6.77         ((k3_enumset1 @ X65 @ X65 @ X66 @ X67 @ X68)
% 6.55/6.77           = (k2_enumset1 @ X65 @ X66 @ X67 @ X68))),
% 6.55/6.77      inference('cnf', [status(esa)], [t72_enumset1])).
% 6.55/6.77  thf(l75_enumset1, axiom,
% 6.55/6.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 6.55/6.77     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 6.55/6.77       ( k2_xboole_0 @
% 6.55/6.77         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 6.55/6.77  thf('15', plain,
% 6.55/6.77      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, 
% 6.55/6.77         X49 : $i]:
% 6.55/6.77         ((k6_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 6.55/6.77           = (k2_xboole_0 @ (k2_enumset1 @ X42 @ X43 @ X44 @ X45) @ 
% 6.55/6.77              (k2_enumset1 @ X46 @ X47 @ X48 @ X49)))),
% 6.55/6.77      inference('cnf', [status(esa)], [l75_enumset1])).
% 6.55/6.77  thf('16', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 6.55/6.77         ((k6_enumset1 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4)
% 6.55/6.77           = (k2_xboole_0 @ (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0) @ 
% 6.55/6.77              (k2_enumset1 @ X7 @ X6 @ X5 @ X4)))),
% 6.55/6.77      inference('sup+', [status(thm)], ['14', '15'])).
% 6.55/6.77  thf(t131_enumset1, axiom,
% 6.55/6.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 6.55/6.77     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 6.55/6.77       ( k2_xboole_0 @
% 6.55/6.77         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_enumset1 @ F @ G @ H @ I ) ) ))).
% 6.55/6.77  thf('17', plain,
% 6.55/6.77      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, 
% 6.55/6.77         X57 : $i, X58 : $i]:
% 6.55/6.77         ((k7_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58)
% 6.55/6.77           = (k2_xboole_0 @ (k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54) @ 
% 6.55/6.77              (k2_enumset1 @ X55 @ X56 @ X57 @ X58)))),
% 6.55/6.77      inference('cnf', [status(esa)], [t131_enumset1])).
% 6.55/6.77  thf('18', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 6.55/6.77         ((k6_enumset1 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4)
% 6.55/6.77           = (k7_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4))),
% 6.55/6.77      inference('demod', [status(thm)], ['16', '17'])).
% 6.55/6.77  thf(d7_enumset1, axiom,
% 6.55/6.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i,J:$i]:
% 6.55/6.77     ( ( ( J ) = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) ) <=>
% 6.55/6.77       ( ![K:$i]:
% 6.55/6.77         ( ( r2_hidden @ K @ J ) <=>
% 6.55/6.77           ( ~( ( ( K ) != ( I ) ) & ( ( K ) != ( H ) ) & ( ( K ) != ( G ) ) & 
% 6.55/6.77                ( ( K ) != ( F ) ) & ( ( K ) != ( E ) ) & ( ( K ) != ( D ) ) & 
% 6.55/6.77                ( ( K ) != ( C ) ) & ( ( K ) != ( B ) ) & ( ( K ) != ( A ) ) ) ) ) ) ))).
% 6.55/6.77  thf(zf_stmt_1, type, zip_tseitin_0 :
% 6.55/6.77      $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 6.55/6.77  thf(zf_stmt_2, axiom,
% 6.55/6.77    (![K:$i,I:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 6.55/6.77     ( ( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 6.55/6.77       ( ( ( K ) != ( A ) ) & ( ( K ) != ( B ) ) & ( ( K ) != ( C ) ) & 
% 6.55/6.77         ( ( K ) != ( D ) ) & ( ( K ) != ( E ) ) & ( ( K ) != ( F ) ) & 
% 6.55/6.77         ( ( K ) != ( G ) ) & ( ( K ) != ( H ) ) & ( ( K ) != ( I ) ) ) ))).
% 6.55/6.77  thf(zf_stmt_3, axiom,
% 6.55/6.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i,J:$i]:
% 6.55/6.77     ( ( ( J ) = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) ) <=>
% 6.55/6.77       ( ![K:$i]:
% 6.55/6.77         ( ( r2_hidden @ K @ J ) <=>
% 6.55/6.77           ( ~( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 6.55/6.77  thf('19', plain,
% 6.55/6.77      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, 
% 6.55/6.77         X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 6.55/6.77         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ 
% 6.55/6.77           X37 @ X38)
% 6.55/6.77          | (r2_hidden @ X29 @ X39)
% 6.55/6.77          | ((X39)
% 6.55/6.77              != (k7_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32 @ 
% 6.55/6.77                  X31 @ X30)))),
% 6.55/6.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.55/6.77  thf('20', plain,
% 6.55/6.77      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, 
% 6.55/6.77         X36 : $i, X37 : $i, X38 : $i]:
% 6.55/6.77         ((r2_hidden @ X29 @ 
% 6.55/6.77           (k7_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32 @ X31 @ X30))
% 6.55/6.77          | (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ 
% 6.55/6.77             X37 @ X38))),
% 6.55/6.77      inference('simplify', [status(thm)], ['19'])).
% 6.55/6.77  thf('21', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 6.55/6.77         X7 : $i, X8 : $i]:
% 6.55/6.77         ((r2_hidden @ X8 @ 
% 6.55/6.77           (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 6.55/6.77          | (zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X7))),
% 6.55/6.77      inference('sup+', [status(thm)], ['18', '20'])).
% 6.55/6.77  thf('22', plain,
% 6.55/6.77      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, 
% 6.55/6.77         X25 : $i, X26 : $i, X27 : $i]:
% 6.55/6.77         (((X19) != (X20))
% 6.55/6.77          | ~ (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ 
% 6.55/6.77               X27 @ X18))),
% 6.55/6.77      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.55/6.77  thf('23', plain,
% 6.55/6.77      (![X18 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 6.55/6.77         X26 : $i, X27 : $i]:
% 6.55/6.77         ~ (zip_tseitin_0 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ 
% 6.55/6.77            X27 @ X18)),
% 6.55/6.77      inference('simplify', [status(thm)], ['22'])).
% 6.55/6.77  thf('24', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 6.55/6.77         (r2_hidden @ X7 @ 
% 6.55/6.77          (k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7))),
% 6.55/6.77      inference('sup-', [status(thm)], ['21', '23'])).
% 6.55/6.77  thf('25', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.55/6.77         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.55/6.77      inference('sup+', [status(thm)], ['13', '24'])).
% 6.55/6.77  thf('26', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 6.55/6.77      inference('sup+', [status(thm)], ['4', '25'])).
% 6.55/6.77  thf(l49_zfmisc_1, axiom,
% 6.55/6.77    (![A:$i,B:$i]:
% 6.55/6.77     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 6.55/6.77  thf('27', plain,
% 6.55/6.77      (![X87 : $i, X88 : $i]:
% 6.55/6.77         ((r1_tarski @ X87 @ (k3_tarski @ X88)) | ~ (r2_hidden @ X87 @ X88))),
% 6.55/6.77      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 6.55/6.77  thf('28', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i]:
% 6.55/6.77         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 6.55/6.77      inference('sup-', [status(thm)], ['26', '27'])).
% 6.55/6.77  thf(l51_zfmisc_1, axiom,
% 6.55/6.77    (![A:$i,B:$i]:
% 6.55/6.77     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 6.55/6.77  thf('29', plain,
% 6.55/6.77      (![X89 : $i, X90 : $i]:
% 6.55/6.77         ((k3_tarski @ (k2_tarski @ X89 @ X90)) = (k2_xboole_0 @ X89 @ X90))),
% 6.55/6.77      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 6.55/6.77  thf('30', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 6.55/6.77      inference('demod', [status(thm)], ['28', '29'])).
% 6.55/6.77  thf(t60_xboole_1, axiom,
% 6.55/6.77    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 6.55/6.77  thf('31', plain,
% 6.55/6.77      (![X7 : $i, X8 : $i]:
% 6.55/6.77         (~ (r1_tarski @ X7 @ X8) | ~ (r2_xboole_0 @ X8 @ X7))),
% 6.55/6.77      inference('cnf', [status(esa)], [t60_xboole_1])).
% 6.55/6.77  thf('32', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i]: ~ (r2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)),
% 6.55/6.77      inference('sup-', [status(thm)], ['30', '31'])).
% 6.55/6.77  thf('33', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 6.55/6.77      inference('sup-', [status(thm)], ['3', '32'])).
% 6.55/6.77  thf(t7_xboole_1, axiom,
% 6.55/6.77    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 6.55/6.77  thf('34', plain,
% 6.55/6.77      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 6.55/6.77      inference('cnf', [status(esa)], [t7_xboole_1])).
% 6.55/6.77  thf(t69_enumset1, axiom,
% 6.55/6.77    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 6.55/6.77  thf('35', plain,
% 6.55/6.77      (![X59 : $i]: ((k2_tarski @ X59 @ X59) = (k1_tarski @ X59))),
% 6.55/6.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.55/6.77  thf(t38_zfmisc_1, axiom,
% 6.55/6.77    (![A:$i,B:$i,C:$i]:
% 6.55/6.77     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 6.55/6.77       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 6.55/6.77  thf('36', plain,
% 6.55/6.77      (![X91 : $i, X92 : $i, X93 : $i]:
% 6.55/6.77         ((r2_hidden @ X91 @ X92)
% 6.55/6.77          | ~ (r1_tarski @ (k2_tarski @ X91 @ X93) @ X92))),
% 6.55/6.77      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 6.55/6.77  thf('37', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i]:
% 6.55/6.77         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 6.55/6.77      inference('sup-', [status(thm)], ['35', '36'])).
% 6.55/6.77  thf('38', plain,
% 6.55/6.77      (![X0 : $i, X1 : $i]:
% 6.55/6.77         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 6.55/6.77      inference('sup-', [status(thm)], ['34', '37'])).
% 6.55/6.77  thf('39', plain, ((r2_hidden @ sk_A @ sk_B)),
% 6.55/6.77      inference('sup+', [status(thm)], ['33', '38'])).
% 6.55/6.77  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 6.55/6.77  
% 6.55/6.77  % SZS output end Refutation
% 6.55/6.77  
% 6.55/6.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
