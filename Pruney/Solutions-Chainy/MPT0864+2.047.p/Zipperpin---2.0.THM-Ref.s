%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gNk682BW2D

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:05 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 334 expanded)
%              Number of leaves         :   35 ( 112 expanded)
%              Depth                    :   22
%              Number of atoms          : 1238 (3454 expanded)
%              Number of equality atoms :  124 ( 378 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(d4_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( ( H != F )
              & ( H != E )
              & ( H != D )
              & ( H != C )
              & ( H != B )
              & ( H != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_1: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [H: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ H @ F @ E @ D @ C @ B @ A )
    <=> ( ( H != A )
        & ( H != B )
        & ( H != C )
        & ( H != D )
        & ( H != E )
        & ( H != F ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( zip_tseitin_1 @ H @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i,X71: $i,X72: $i,X73: $i,X74: $i] :
      ( ( zip_tseitin_1 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 )
      | ( r2_hidden @ X67 @ X74 )
      | ( X74
       != ( k4_enumset1 @ X73 @ X72 @ X71 @ X70 @ X69 @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i,X71: $i,X72: $i,X73: $i] :
      ( ( r2_hidden @ X67 @ ( k4_enumset1 @ X73 @ X72 @ X71 @ X70 @ X69 @ X68 ) )
      | ( zip_tseitin_1 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_1 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ( X60 != X59 )
      | ~ ( zip_tseitin_1 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X59: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ~ ( zip_tseitin_1 @ X59 @ X61 @ X62 @ X63 @ X64 @ X65 @ X59 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ( zip_tseitin_1 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 )
      | ( X60 = X61 )
      | ( X60 = X62 )
      | ( X60 = X63 )
      | ( X60 = X64 )
      | ( X60 = X65 )
      | ( X60 = X66 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('21',plain,(
    ! [X68: $i,X69: $i,X70: $i,X71: $i,X72: $i,X73: $i,X74: $i,X75: $i] :
      ( ~ ( r2_hidden @ X75 @ X74 )
      | ~ ( zip_tseitin_1 @ X75 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 )
      | ( X74
       != ( k4_enumset1 @ X73 @ X72 @ X71 @ X70 @ X69 @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,(
    ! [X68: $i,X69: $i,X70: $i,X71: $i,X72: $i,X73: $i,X75: $i] :
      ( ~ ( zip_tseitin_1 @ X75 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 )
      | ~ ( r2_hidden @ X75 @ ( k4_enumset1 @ X73 @ X72 @ X71 @ X70 @ X69 @ X68 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_1 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_1 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('35',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X50 ) @ X52 )
      | ~ ( r2_hidden @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('37',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('41',plain,(
    ! [X77: $i,X78: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X77 @ X78 ) )
      = X77 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('42',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('45',plain,(
    ! [X77: $i,X79: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X77 @ X79 ) )
      = X79 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('46',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,
    ( ( sk_A
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('50',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X55 ) @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_tarski @ ( k4_tarski @ X55 @ X56 ) @ ( k4_tarski @ X55 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('54',plain,(
    ! [X53: $i,X54: $i] :
      ( ( X53 = k1_xboole_0 )
      | ~ ( r1_tarski @ X53 @ ( k2_zfmisc_1 @ X54 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','56'])).

thf('58',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('60',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['44','45'])).

thf('61',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('62',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('63',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('66',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X55 ) @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_tarski @ ( k4_tarski @ X55 @ X56 ) @ ( k4_tarski @ X55 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ ( k2_mcart_1 @ sk_A ) @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ X0 ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X53: $i,X54: $i] :
      ( ( X53 = k1_xboole_0 )
      | ~ ( r1_tarski @ X53 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ X0 ) ) )
        | ( ( k1_tarski @ sk_A )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('72',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','72'])).

thf('74',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('76',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X4: $i] :
      ( ( r1_xboole_0 @ X4 @ X4 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('78',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('94',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X4: $i] :
      ~ ( r2_hidden @ X4 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','96'])).

thf('98',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('99',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['58','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('102',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('106',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference('sup-',[status(thm)],['14','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gNk682BW2D
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:43:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.05/1.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.25  % Solved by: fo/fo7.sh
% 1.05/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.25  % done 1108 iterations in 0.792s
% 1.05/1.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.25  % SZS output start Refutation
% 1.05/1.25  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.05/1.25  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.05/1.25  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.05/1.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.25  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.05/1.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.25  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $i > $i > $i > $o).
% 1.05/1.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.05/1.25  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.05/1.25  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.05/1.25  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.05/1.25  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.05/1.25  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.05/1.25  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.05/1.25  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.05/1.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.25  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.05/1.25  thf(t70_enumset1, axiom,
% 1.05/1.25    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.05/1.25  thf('0', plain,
% 1.05/1.25      (![X7 : $i, X8 : $i]:
% 1.05/1.25         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 1.05/1.25      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.05/1.25  thf(t69_enumset1, axiom,
% 1.05/1.25    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.05/1.25  thf('1', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.05/1.25      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.05/1.25  thf('2', plain,
% 1.05/1.25      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['0', '1'])).
% 1.05/1.25  thf(t71_enumset1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.05/1.25  thf('3', plain,
% 1.05/1.25      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.05/1.25         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 1.05/1.25      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.05/1.25  thf(t72_enumset1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.25     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.05/1.25  thf('4', plain,
% 1.05/1.25      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.05/1.25         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 1.05/1.25           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 1.05/1.25      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.05/1.25  thf(t73_enumset1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.05/1.25     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.05/1.25       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.05/1.25  thf('5', plain,
% 1.05/1.25      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.25         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 1.05/1.25           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 1.05/1.25      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.05/1.25  thf(d4_enumset1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.05/1.25     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 1.05/1.25       ( ![H:$i]:
% 1.05/1.25         ( ( r2_hidden @ H @ G ) <=>
% 1.05/1.25           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 1.05/1.25                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 1.05/1.25  thf(zf_stmt_0, type, zip_tseitin_1 : $i > $i > $i > $i > $i > $i > $i > $o).
% 1.05/1.25  thf(zf_stmt_1, axiom,
% 1.05/1.25    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 1.05/1.25     ( ( zip_tseitin_1 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 1.05/1.25       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 1.05/1.25         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 1.05/1.25  thf(zf_stmt_2, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.05/1.25     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 1.05/1.25       ( ![H:$i]:
% 1.05/1.25         ( ( r2_hidden @ H @ G ) <=>
% 1.05/1.25           ( ~( zip_tseitin_1 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 1.05/1.25  thf('6', plain,
% 1.05/1.25      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i, 
% 1.05/1.25         X74 : $i]:
% 1.05/1.25         ((zip_tseitin_1 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73)
% 1.05/1.25          | (r2_hidden @ X67 @ X74)
% 1.05/1.25          | ((X74) != (k4_enumset1 @ X73 @ X72 @ X71 @ X70 @ X69 @ X68)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.05/1.25  thf('7', plain,
% 1.05/1.25      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i]:
% 1.05/1.25         ((r2_hidden @ X67 @ (k4_enumset1 @ X73 @ X72 @ X71 @ X70 @ X69 @ X68))
% 1.05/1.25          | (zip_tseitin_1 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73))),
% 1.05/1.25      inference('simplify', [status(thm)], ['6'])).
% 1.05/1.25  thf('8', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.05/1.25         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.05/1.25          | (zip_tseitin_1 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 1.05/1.25      inference('sup+', [status(thm)], ['5', '7'])).
% 1.05/1.25  thf('9', plain,
% 1.05/1.25      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 1.05/1.25         (((X60) != (X59))
% 1.05/1.25          | ~ (zip_tseitin_1 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 @ X59))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.05/1.25  thf('10', plain,
% 1.05/1.25      (![X59 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 1.05/1.25         ~ (zip_tseitin_1 @ X59 @ X61 @ X62 @ X63 @ X64 @ X65 @ X59)),
% 1.05/1.25      inference('simplify', [status(thm)], ['9'])).
% 1.05/1.25  thf('11', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.05/1.25         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 1.05/1.25      inference('sup-', [status(thm)], ['8', '10'])).
% 1.05/1.25  thf('12', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.05/1.25         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['4', '11'])).
% 1.05/1.25  thf('13', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.25         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['3', '12'])).
% 1.05/1.25  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['2', '13'])).
% 1.05/1.25  thf('15', plain,
% 1.05/1.25      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 1.05/1.25         ((zip_tseitin_1 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66)
% 1.05/1.25          | ((X60) = (X61))
% 1.05/1.25          | ((X60) = (X62))
% 1.05/1.25          | ((X60) = (X63))
% 1.05/1.25          | ((X60) = (X64))
% 1.05/1.25          | ((X60) = (X65))
% 1.05/1.25          | ((X60) = (X66)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.05/1.25  thf(t3_xboole_0, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.05/1.25            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.05/1.25       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.05/1.25            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.05/1.25  thf('16', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.05/1.25      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.25  thf('17', plain,
% 1.05/1.25      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['0', '1'])).
% 1.05/1.25  thf('18', plain,
% 1.05/1.25      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.05/1.25         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 1.05/1.25      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.05/1.25  thf('19', plain,
% 1.05/1.25      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.05/1.25         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 1.05/1.25           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 1.05/1.25      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.05/1.25  thf('20', plain,
% 1.05/1.25      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.25         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 1.05/1.25           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 1.05/1.25      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.05/1.25  thf('21', plain,
% 1.05/1.25      (![X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i, X74 : $i, 
% 1.05/1.25         X75 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X75 @ X74)
% 1.05/1.25          | ~ (zip_tseitin_1 @ X75 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73)
% 1.05/1.25          | ((X74) != (k4_enumset1 @ X73 @ X72 @ X71 @ X70 @ X69 @ X68)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.05/1.25  thf('22', plain,
% 1.05/1.25      (![X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i, X75 : $i]:
% 1.05/1.25         (~ (zip_tseitin_1 @ X75 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73)
% 1.05/1.25          | ~ (r2_hidden @ X75 @ 
% 1.05/1.25               (k4_enumset1 @ X73 @ X72 @ X71 @ X70 @ X69 @ X68)))),
% 1.05/1.25      inference('simplify', [status(thm)], ['21'])).
% 1.05/1.25  thf('23', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.05/1.25          | ~ (zip_tseitin_1 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 1.05/1.25      inference('sup-', [status(thm)], ['20', '22'])).
% 1.05/1.25  thf('24', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 1.05/1.25          | ~ (zip_tseitin_1 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3))),
% 1.05/1.25      inference('sup-', [status(thm)], ['19', '23'])).
% 1.05/1.25  thf('25', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 1.05/1.25          | ~ (zip_tseitin_1 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2))),
% 1.05/1.25      inference('sup-', [status(thm)], ['18', '24'])).
% 1.05/1.25  thf('26', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.05/1.25          | ~ (zip_tseitin_1 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['17', '25'])).
% 1.05/1.25  thf('27', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.05/1.25          | ~ (zip_tseitin_1 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0 @ 
% 1.05/1.25               X0 @ X0 @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['16', '26'])).
% 1.05/1.25  thf('28', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.05/1.25          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.05/1.25          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.05/1.25          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.05/1.25          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.05/1.25          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.05/1.25          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.05/1.25      inference('sup-', [status(thm)], ['15', '27'])).
% 1.05/1.25  thf('29', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.05/1.25          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.05/1.25      inference('simplify', [status(thm)], ['28'])).
% 1.05/1.25  thf('30', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 1.05/1.25      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.25  thf('31', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r2_hidden @ X0 @ X1)
% 1.05/1.25          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.05/1.25          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.05/1.25      inference('sup+', [status(thm)], ['29', '30'])).
% 1.05/1.25  thf('32', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 1.05/1.25      inference('simplify', [status(thm)], ['31'])).
% 1.05/1.25  thf(t66_xboole_1, axiom,
% 1.05/1.25    (![A:$i]:
% 1.05/1.25     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 1.05/1.25       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.05/1.25  thf('33', plain,
% 1.05/1.25      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X5))),
% 1.05/1.25      inference('cnf', [status(esa)], [t66_xboole_1])).
% 1.05/1.25  thf('34', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.05/1.25          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['32', '33'])).
% 1.05/1.25  thf(l1_zfmisc_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.05/1.25  thf('35', plain,
% 1.05/1.25      (![X50 : $i, X52 : $i]:
% 1.05/1.25         ((r1_tarski @ (k1_tarski @ X50) @ X52) | ~ (r2_hidden @ X50 @ X52))),
% 1.05/1.25      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.05/1.25  thf('36', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (((k1_tarski @ X0) = (k1_xboole_0))
% 1.05/1.25          | (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['34', '35'])).
% 1.05/1.25  thf(t20_mcart_1, conjecture,
% 1.05/1.25    (![A:$i]:
% 1.05/1.25     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 1.05/1.25       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 1.05/1.25  thf(zf_stmt_3, negated_conjecture,
% 1.05/1.25    (~( ![A:$i]:
% 1.05/1.25        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 1.05/1.25          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 1.05/1.25    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 1.05/1.25  thf('37', plain,
% 1.05/1.25      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.05/1.25  thf('38', plain,
% 1.05/1.25      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('split', [status(esa)], ['37'])).
% 1.05/1.25  thf('39', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C_1))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.05/1.25  thf('40', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C_1))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.05/1.25  thf(t7_mcart_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 1.05/1.25       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 1.05/1.25  thf('41', plain,
% 1.05/1.25      (![X77 : $i, X78 : $i]: ((k1_mcart_1 @ (k4_tarski @ X77 @ X78)) = (X77))),
% 1.05/1.25      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.05/1.25  thf('42', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 1.05/1.25      inference('sup+', [status(thm)], ['40', '41'])).
% 1.05/1.25  thf('43', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_1))),
% 1.05/1.25      inference('demod', [status(thm)], ['39', '42'])).
% 1.05/1.25  thf('44', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_1))),
% 1.05/1.25      inference('demod', [status(thm)], ['39', '42'])).
% 1.05/1.25  thf('45', plain,
% 1.05/1.25      (![X77 : $i, X79 : $i]: ((k2_mcart_1 @ (k4_tarski @ X77 @ X79)) = (X79))),
% 1.05/1.25      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.05/1.25  thf('46', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 1.05/1.25      inference('sup+', [status(thm)], ['44', '45'])).
% 1.05/1.25  thf('47', plain,
% 1.05/1.25      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 1.05/1.25      inference('demod', [status(thm)], ['43', '46'])).
% 1.05/1.25  thf('48', plain,
% 1.05/1.25      ((((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_A)))
% 1.05/1.25         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['38', '47'])).
% 1.05/1.25  thf('49', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.05/1.25      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.05/1.25  thf(t36_zfmisc_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 1.05/1.25         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 1.05/1.25       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 1.05/1.25         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 1.05/1.25  thf('50', plain,
% 1.05/1.25      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.05/1.25         ((k2_zfmisc_1 @ (k1_tarski @ X55) @ (k2_tarski @ X56 @ X57))
% 1.05/1.25           = (k2_tarski @ (k4_tarski @ X55 @ X56) @ (k4_tarski @ X55 @ X57)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 1.05/1.25  thf('51', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 1.05/1.25           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 1.05/1.25      inference('sup+', [status(thm)], ['49', '50'])).
% 1.05/1.25  thf('52', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.05/1.25      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.05/1.25  thf('53', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.05/1.25           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 1.05/1.25      inference('demod', [status(thm)], ['51', '52'])).
% 1.05/1.25  thf(t135_zfmisc_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 1.05/1.25         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.05/1.25       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.05/1.25  thf('54', plain,
% 1.05/1.25      (![X53 : $i, X54 : $i]:
% 1.05/1.25         (((X53) = (k1_xboole_0))
% 1.05/1.25          | ~ (r1_tarski @ X53 @ (k2_zfmisc_1 @ X54 @ X53)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 1.05/1.25  thf('55', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 1.05/1.25          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['53', '54'])).
% 1.05/1.25  thf('56', plain,
% 1.05/1.25      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 1.05/1.25         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 1.05/1.25         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['48', '55'])).
% 1.05/1.25  thf('57', plain,
% 1.05/1.25      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 1.05/1.25         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 1.05/1.25         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['36', '56'])).
% 1.05/1.25  thf('58', plain,
% 1.05/1.25      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 1.05/1.25         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('simplify', [status(thm)], ['57'])).
% 1.05/1.25  thf('59', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (((k1_tarski @ X0) = (k1_xboole_0))
% 1.05/1.25          | (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['34', '35'])).
% 1.05/1.25  thf('60', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 1.05/1.25      inference('sup+', [status(thm)], ['44', '45'])).
% 1.05/1.25  thf('61', plain,
% 1.05/1.25      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('split', [status(esa)], ['37'])).
% 1.05/1.25  thf('62', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_1))),
% 1.05/1.25      inference('demod', [status(thm)], ['39', '42'])).
% 1.05/1.25  thf('63', plain,
% 1.05/1.25      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_1)))
% 1.05/1.25         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['61', '62'])).
% 1.05/1.25  thf('64', plain,
% 1.05/1.25      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 1.05/1.25         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['60', '63'])).
% 1.05/1.25  thf('65', plain,
% 1.05/1.25      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 1.05/1.25         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['60', '63'])).
% 1.05/1.25  thf('66', plain,
% 1.05/1.25      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.05/1.25         ((k2_zfmisc_1 @ (k1_tarski @ X55) @ (k2_tarski @ X56 @ X57))
% 1.05/1.25           = (k2_tarski @ (k4_tarski @ X55 @ X56) @ (k4_tarski @ X55 @ X57)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 1.05/1.25  thf('67', plain,
% 1.05/1.25      ((![X0 : $i]:
% 1.05/1.25          ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ 
% 1.05/1.25            (k2_tarski @ (k2_mcart_1 @ sk_A) @ X0))
% 1.05/1.25            = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ X0))))
% 1.05/1.25         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['65', '66'])).
% 1.05/1.25  thf('68', plain,
% 1.05/1.25      (![X53 : $i, X54 : $i]:
% 1.05/1.25         (((X53) = (k1_xboole_0))
% 1.05/1.25          | ~ (r1_tarski @ X53 @ (k2_zfmisc_1 @ X53 @ X54)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 1.05/1.25  thf('69', plain,
% 1.05/1.25      ((![X0 : $i]:
% 1.05/1.25          (~ (r1_tarski @ (k1_tarski @ sk_A) @ 
% 1.05/1.25              (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ X0)))
% 1.05/1.25           | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 1.05/1.25         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['67', '68'])).
% 1.05/1.25  thf('70', plain,
% 1.05/1.25      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_A))
% 1.05/1.25         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 1.05/1.25         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['64', '69'])).
% 1.05/1.25  thf('71', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.05/1.25      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.05/1.25  thf('72', plain,
% 1.05/1.25      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 1.05/1.25         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 1.05/1.25         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('demod', [status(thm)], ['70', '71'])).
% 1.05/1.25  thf('73', plain,
% 1.05/1.25      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 1.05/1.25         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 1.05/1.25         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['59', '72'])).
% 1.05/1.25  thf('74', plain,
% 1.05/1.25      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 1.05/1.25         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('simplify', [status(thm)], ['73'])).
% 1.05/1.25  thf('75', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['2', '13'])).
% 1.05/1.25  thf('76', plain,
% 1.05/1.25      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['74', '75'])).
% 1.05/1.25  thf('77', plain,
% 1.05/1.25      (![X4 : $i]: ((r1_xboole_0 @ X4 @ X4) | ((X4) != (k1_xboole_0)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t66_xboole_1])).
% 1.05/1.25  thf('78', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 1.05/1.25      inference('simplify', [status(thm)], ['77'])).
% 1.05/1.25  thf('79', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.05/1.25      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.25  thf('80', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.05/1.25      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.25  thf('81', plain,
% 1.05/1.25      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X2 @ X0)
% 1.05/1.25          | ~ (r2_hidden @ X2 @ X3)
% 1.05/1.25          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.05/1.25      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.25  thf('82', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.25         ((r1_xboole_0 @ X0 @ X1)
% 1.05/1.25          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.05/1.25          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 1.05/1.25      inference('sup-', [status(thm)], ['80', '81'])).
% 1.05/1.25  thf('83', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r1_xboole_0 @ X0 @ X1)
% 1.05/1.25          | ~ (r1_xboole_0 @ X0 @ X0)
% 1.05/1.25          | (r1_xboole_0 @ X0 @ X1))),
% 1.05/1.25      inference('sup-', [status(thm)], ['79', '82'])).
% 1.05/1.25  thf('84', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.05/1.25      inference('simplify', [status(thm)], ['83'])).
% 1.05/1.25  thf('85', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.05/1.25      inference('sup-', [status(thm)], ['78', '84'])).
% 1.05/1.25  thf('86', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.05/1.25      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.25  thf('87', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 1.05/1.25      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.25  thf('88', plain,
% 1.05/1.25      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X2 @ X0)
% 1.05/1.25          | ~ (r2_hidden @ X2 @ X3)
% 1.05/1.25          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.05/1.25      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.25  thf('89', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.25         ((r1_xboole_0 @ X1 @ X0)
% 1.05/1.25          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.05/1.25          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 1.05/1.25      inference('sup-', [status(thm)], ['87', '88'])).
% 1.05/1.25  thf('90', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((r1_xboole_0 @ X0 @ X1)
% 1.05/1.25          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.05/1.25          | (r1_xboole_0 @ X0 @ X1))),
% 1.05/1.25      inference('sup-', [status(thm)], ['86', '89'])).
% 1.05/1.25  thf('91', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.05/1.25      inference('simplify', [status(thm)], ['90'])).
% 1.05/1.25  thf('92', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.05/1.25      inference('sup-', [status(thm)], ['85', '91'])).
% 1.05/1.25  thf('93', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.05/1.25         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 1.05/1.25      inference('sup-', [status(thm)], ['8', '10'])).
% 1.05/1.25  thf('94', plain,
% 1.05/1.25      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X2 @ X0)
% 1.05/1.25          | ~ (r2_hidden @ X2 @ X3)
% 1.05/1.25          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.05/1.25      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.25  thf('95', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.05/1.25         (~ (r1_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 1.05/1.25          | ~ (r2_hidden @ X4 @ X5))),
% 1.05/1.25      inference('sup-', [status(thm)], ['93', '94'])).
% 1.05/1.25  thf('96', plain, (![X4 : $i]: ~ (r2_hidden @ X4 @ k1_xboole_0)),
% 1.05/1.25      inference('sup-', [status(thm)], ['92', '95'])).
% 1.05/1.25  thf('97', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['76', '96'])).
% 1.05/1.25  thf('98', plain,
% 1.05/1.25      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 1.05/1.25      inference('split', [status(esa)], ['37'])).
% 1.05/1.25  thf('99', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 1.05/1.25      inference('sat_resolution*', [status(thm)], ['97', '98'])).
% 1.05/1.25  thf('100', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 1.05/1.25      inference('simpl_trail', [status(thm)], ['58', '99'])).
% 1.05/1.25  thf('101', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['2', '13'])).
% 1.05/1.25  thf('102', plain,
% 1.05/1.25      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X2 @ X0)
% 1.05/1.25          | ~ (r2_hidden @ X2 @ X3)
% 1.05/1.25          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.05/1.25      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.25  thf('103', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.05/1.25      inference('sup-', [status(thm)], ['101', '102'])).
% 1.05/1.25  thf('104', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['100', '103'])).
% 1.05/1.25  thf('105', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.05/1.25      inference('sup-', [status(thm)], ['78', '84'])).
% 1.05/1.25  thf('106', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 1.05/1.25      inference('demod', [status(thm)], ['104', '105'])).
% 1.05/1.25  thf('107', plain, ($false), inference('sup-', [status(thm)], ['14', '106'])).
% 1.05/1.25  
% 1.05/1.25  % SZS output end Refutation
% 1.05/1.25  
% 1.09/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
