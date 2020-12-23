%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OapaGY0nb5

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:08 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 241 expanded)
%              Number of leaves         :   35 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  876 (2322 expanded)
%              Number of equality atoms :   92 ( 255 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('6',plain,(
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
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [H: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A )
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
        <=> ~ ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( zip_tseitin_0 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 )
      | ( r2_hidden @ X51 @ X58 )
      | ( X58
       != ( k4_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( r2_hidden @ X51 @ ( k4_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 ) )
      | ( zip_tseitin_0 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X44 != X43 )
      | ~ ( zip_tseitin_0 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X43: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ~ ( zip_tseitin_0 @ X43 @ X45 @ X46 @ X47 @ X48 @ X49 @ X43 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('17',plain,(
    ! [X36: $i,X37: $i,X38: $i,X40: $i] :
      ( ( r1_tarski @ X40 @ ( k1_enumset1 @ X36 @ X37 @ X38 ) )
      | ( X40
       != ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('18',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( r1_tarski @ ( k1_tarski @ X36 ) @ ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','19'])).

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

thf('21',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('25',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X61 @ X62 ) )
      = X61 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('26',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('29',plain,(
    ! [X61: $i,X63: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X61 @ X63 ) )
      = X63 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('30',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( sk_A
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','31'])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X41 ) @ ( k1_tarski @ X42 ) )
      = ( k1_tarski @ ( k4_tarski @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34 = k1_xboole_0 )
      | ~ ( r1_tarski @ X34 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','19'])).

thf('39',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('40',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('41',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X41 ) @ ( k1_tarski @ X42 ) )
      = ( k1_tarski @ ( k4_tarski @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('43',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34 = k1_xboole_0 )
      | ~ ( r1_tarski @ X34 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X4: $i] :
      ( ( r1_xboole_0 @ X4 @ X4 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('50',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

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

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('66',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X4: $i] :
      ~ ( r2_hidden @ X4 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','68'])).

thf('70',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('71',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('74',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('78',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference('sup-',[status(thm)],['14','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OapaGY0nb5
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.19/1.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.19/1.38  % Solved by: fo/fo7.sh
% 1.19/1.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.38  % done 1868 iterations in 0.926s
% 1.19/1.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.19/1.38  % SZS output start Refutation
% 1.19/1.38  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.19/1.38  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.19/1.38  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.19/1.38  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.19/1.38  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.38  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.19/1.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.19/1.38  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.38  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.19/1.38  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.19/1.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.38  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.19/1.38  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.19/1.38  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 1.19/1.38  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.19/1.38  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.19/1.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.19/1.38  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.19/1.38  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.19/1.38  thf(t71_enumset1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i]:
% 1.19/1.38     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.19/1.38  thf('0', plain,
% 1.19/1.38      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.19/1.38         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 1.19/1.38      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.19/1.38  thf(t70_enumset1, axiom,
% 1.19/1.38    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.19/1.38  thf('1', plain,
% 1.19/1.38      (![X7 : $i, X8 : $i]:
% 1.19/1.38         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 1.19/1.38      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.19/1.38  thf('2', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['0', '1'])).
% 1.19/1.38  thf(t69_enumset1, axiom,
% 1.19/1.38    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.19/1.38  thf('3', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.19/1.38      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.19/1.38  thf('4', plain,
% 1.19/1.38      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['2', '3'])).
% 1.19/1.38  thf(t72_enumset1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.38     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.19/1.38  thf('5', plain,
% 1.19/1.38      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.19/1.38         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 1.19/1.38           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 1.19/1.38      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.19/1.38  thf(t73_enumset1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.19/1.38     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.19/1.38       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.19/1.38  thf('6', plain,
% 1.19/1.38      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.19/1.38         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 1.19/1.38           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 1.19/1.38      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.19/1.38  thf(d4_enumset1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.19/1.38     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 1.19/1.38       ( ![H:$i]:
% 1.19/1.38         ( ( r2_hidden @ H @ G ) <=>
% 1.19/1.38           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 1.19/1.38                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 1.19/1.38  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 1.19/1.38  thf(zf_stmt_1, axiom,
% 1.19/1.38    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 1.19/1.38     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 1.19/1.38       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 1.19/1.38         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 1.19/1.38  thf(zf_stmt_2, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.19/1.38     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 1.19/1.38       ( ![H:$i]:
% 1.19/1.38         ( ( r2_hidden @ H @ G ) <=>
% 1.19/1.38           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 1.19/1.38  thf('7', plain,
% 1.19/1.38      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, 
% 1.19/1.38         X58 : $i]:
% 1.19/1.38         ((zip_tseitin_0 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57)
% 1.19/1.38          | (r2_hidden @ X51 @ X58)
% 1.19/1.38          | ((X58) != (k4_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52)))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.19/1.38  thf('8', plain,
% 1.19/1.38      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 1.19/1.38         ((r2_hidden @ X51 @ (k4_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52))
% 1.19/1.38          | (zip_tseitin_0 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57))),
% 1.19/1.38      inference('simplify', [status(thm)], ['7'])).
% 1.19/1.38  thf('9', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.19/1.38         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.19/1.38          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 1.19/1.38      inference('sup+', [status(thm)], ['6', '8'])).
% 1.19/1.38  thf('10', plain,
% 1.19/1.38      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.19/1.38         (((X44) != (X43))
% 1.19/1.38          | ~ (zip_tseitin_0 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X43))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.19/1.38  thf('11', plain,
% 1.19/1.38      (![X43 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.19/1.38         ~ (zip_tseitin_0 @ X43 @ X45 @ X46 @ X47 @ X48 @ X49 @ X43)),
% 1.19/1.38      inference('simplify', [status(thm)], ['10'])).
% 1.19/1.38  thf('12', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.19/1.38         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 1.19/1.38      inference('sup-', [status(thm)], ['9', '11'])).
% 1.19/1.38  thf('13', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.38         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['5', '12'])).
% 1.19/1.38  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['4', '13'])).
% 1.19/1.38  thf('15', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.19/1.38      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.19/1.38  thf('16', plain,
% 1.19/1.38      (![X7 : $i, X8 : $i]:
% 1.19/1.38         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 1.19/1.38      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.19/1.38  thf(t142_zfmisc_1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.38     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.19/1.38       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 1.19/1.38            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 1.19/1.38            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 1.19/1.38            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 1.19/1.38            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 1.19/1.38            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 1.19/1.38  thf('17', plain,
% 1.19/1.38      (![X36 : $i, X37 : $i, X38 : $i, X40 : $i]:
% 1.19/1.38         ((r1_tarski @ X40 @ (k1_enumset1 @ X36 @ X37 @ X38))
% 1.19/1.38          | ((X40) != (k1_tarski @ X36)))),
% 1.19/1.38      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 1.19/1.38  thf('18', plain,
% 1.19/1.38      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.19/1.38         (r1_tarski @ (k1_tarski @ X36) @ (k1_enumset1 @ X36 @ X37 @ X38))),
% 1.19/1.38      inference('simplify', [status(thm)], ['17'])).
% 1.19/1.38  thf('19', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['16', '18'])).
% 1.19/1.38  thf('20', plain,
% 1.19/1.38      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['15', '19'])).
% 1.19/1.38  thf(t20_mcart_1, conjecture,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 1.19/1.38       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 1.19/1.38  thf(zf_stmt_3, negated_conjecture,
% 1.19/1.38    (~( ![A:$i]:
% 1.19/1.38        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 1.19/1.38          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 1.19/1.38    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 1.19/1.38  thf('21', plain,
% 1.19/1.38      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.19/1.38  thf('22', plain,
% 1.19/1.38      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.19/1.38      inference('split', [status(esa)], ['21'])).
% 1.19/1.38  thf('23', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C_1))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.19/1.38  thf('24', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C_1))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.19/1.38  thf(t7_mcart_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 1.19/1.38       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 1.19/1.38  thf('25', plain,
% 1.19/1.38      (![X61 : $i, X62 : $i]: ((k1_mcart_1 @ (k4_tarski @ X61 @ X62)) = (X61))),
% 1.19/1.38      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.19/1.38  thf('26', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 1.19/1.38      inference('sup+', [status(thm)], ['24', '25'])).
% 1.19/1.38  thf('27', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_1))),
% 1.19/1.38      inference('demod', [status(thm)], ['23', '26'])).
% 1.19/1.38  thf('28', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_1))),
% 1.19/1.38      inference('demod', [status(thm)], ['23', '26'])).
% 1.19/1.38  thf('29', plain,
% 1.19/1.38      (![X61 : $i, X63 : $i]: ((k2_mcart_1 @ (k4_tarski @ X61 @ X63)) = (X63))),
% 1.19/1.38      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.19/1.38  thf('30', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 1.19/1.38      inference('sup+', [status(thm)], ['28', '29'])).
% 1.19/1.38  thf('31', plain,
% 1.19/1.38      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 1.19/1.38      inference('demod', [status(thm)], ['27', '30'])).
% 1.19/1.38  thf('32', plain,
% 1.19/1.38      ((((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_A)))
% 1.19/1.38         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.19/1.38      inference('sup+', [status(thm)], ['22', '31'])).
% 1.19/1.38  thf(t35_zfmisc_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.19/1.38       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 1.19/1.38  thf('33', plain,
% 1.19/1.38      (![X41 : $i, X42 : $i]:
% 1.19/1.38         ((k2_zfmisc_1 @ (k1_tarski @ X41) @ (k1_tarski @ X42))
% 1.19/1.38           = (k1_tarski @ (k4_tarski @ X41 @ X42)))),
% 1.19/1.38      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 1.19/1.38  thf(t135_zfmisc_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 1.19/1.38         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.19/1.38       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.19/1.38  thf('34', plain,
% 1.19/1.38      (![X34 : $i, X35 : $i]:
% 1.19/1.38         (((X34) = (k1_xboole_0))
% 1.19/1.38          | ~ (r1_tarski @ X34 @ (k2_zfmisc_1 @ X35 @ X34)))),
% 1.19/1.38      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 1.19/1.38  thf('35', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 1.19/1.38          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['33', '34'])).
% 1.19/1.38  thf('36', plain,
% 1.19/1.38      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 1.19/1.38         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 1.19/1.38         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.19/1.38      inference('sup-', [status(thm)], ['32', '35'])).
% 1.19/1.38  thf('37', plain,
% 1.19/1.38      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 1.19/1.38         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.19/1.38      inference('sup-', [status(thm)], ['20', '36'])).
% 1.19/1.38  thf('38', plain,
% 1.19/1.38      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['15', '19'])).
% 1.19/1.38  thf('39', plain,
% 1.19/1.38      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.19/1.38      inference('split', [status(esa)], ['21'])).
% 1.19/1.38  thf('40', plain,
% 1.19/1.38      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 1.19/1.38      inference('demod', [status(thm)], ['27', '30'])).
% 1.19/1.38  thf('41', plain,
% 1.19/1.38      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 1.19/1.38         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.19/1.38      inference('sup+', [status(thm)], ['39', '40'])).
% 1.19/1.38  thf('42', plain,
% 1.19/1.38      (![X41 : $i, X42 : $i]:
% 1.19/1.38         ((k2_zfmisc_1 @ (k1_tarski @ X41) @ (k1_tarski @ X42))
% 1.19/1.38           = (k1_tarski @ (k4_tarski @ X41 @ X42)))),
% 1.19/1.38      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 1.19/1.38  thf('43', plain,
% 1.19/1.38      (![X34 : $i, X35 : $i]:
% 1.19/1.38         (((X34) = (k1_xboole_0))
% 1.19/1.38          | ~ (r1_tarski @ X34 @ (k2_zfmisc_1 @ X34 @ X35)))),
% 1.19/1.38      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 1.19/1.38  thf('44', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 1.19/1.38          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['42', '43'])).
% 1.19/1.38  thf('45', plain,
% 1.19/1.38      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 1.19/1.38         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 1.19/1.38         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.19/1.38      inference('sup-', [status(thm)], ['41', '44'])).
% 1.19/1.38  thf('46', plain,
% 1.19/1.38      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 1.19/1.38         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.19/1.38      inference('sup-', [status(thm)], ['38', '45'])).
% 1.19/1.38  thf('47', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['4', '13'])).
% 1.19/1.38  thf('48', plain,
% 1.19/1.38      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.19/1.38      inference('sup+', [status(thm)], ['46', '47'])).
% 1.19/1.38  thf(t66_xboole_1, axiom,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 1.19/1.38       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.19/1.38  thf('49', plain,
% 1.19/1.38      (![X4 : $i]: ((r1_xboole_0 @ X4 @ X4) | ((X4) != (k1_xboole_0)))),
% 1.19/1.38      inference('cnf', [status(esa)], [t66_xboole_1])).
% 1.19/1.38  thf('50', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 1.19/1.38      inference('simplify', [status(thm)], ['49'])).
% 1.19/1.38  thf(t3_xboole_0, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.19/1.38            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.19/1.38       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.19/1.38            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.19/1.38  thf('51', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.19/1.38      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.19/1.38  thf('52', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.19/1.38      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.19/1.38  thf('53', plain,
% 1.19/1.38      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.19/1.38         (~ (r2_hidden @ X2 @ X0)
% 1.19/1.38          | ~ (r2_hidden @ X2 @ X3)
% 1.19/1.38          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.19/1.38      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.19/1.38  thf('54', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.38         ((r1_xboole_0 @ X0 @ X1)
% 1.19/1.38          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.19/1.38          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 1.19/1.38      inference('sup-', [status(thm)], ['52', '53'])).
% 1.19/1.38  thf('55', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((r1_xboole_0 @ X0 @ X1)
% 1.19/1.38          | ~ (r1_xboole_0 @ X0 @ X0)
% 1.19/1.38          | (r1_xboole_0 @ X0 @ X1))),
% 1.19/1.38      inference('sup-', [status(thm)], ['51', '54'])).
% 1.19/1.38  thf('56', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.19/1.38      inference('simplify', [status(thm)], ['55'])).
% 1.19/1.38  thf('57', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.19/1.38      inference('sup-', [status(thm)], ['50', '56'])).
% 1.19/1.38  thf('58', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.19/1.38      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.19/1.38  thf('59', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 1.19/1.38      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.19/1.38  thf('60', plain,
% 1.19/1.38      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.19/1.38         (~ (r2_hidden @ X2 @ X0)
% 1.19/1.38          | ~ (r2_hidden @ X2 @ X3)
% 1.19/1.38          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.19/1.38      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.19/1.38  thf('61', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.38         ((r1_xboole_0 @ X1 @ X0)
% 1.19/1.38          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.19/1.38          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 1.19/1.38      inference('sup-', [status(thm)], ['59', '60'])).
% 1.19/1.38  thf('62', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((r1_xboole_0 @ X0 @ X1)
% 1.19/1.38          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.19/1.38          | (r1_xboole_0 @ X0 @ X1))),
% 1.19/1.38      inference('sup-', [status(thm)], ['58', '61'])).
% 1.19/1.38  thf('63', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.19/1.38      inference('simplify', [status(thm)], ['62'])).
% 1.19/1.38  thf('64', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.19/1.38      inference('sup-', [status(thm)], ['57', '63'])).
% 1.19/1.38  thf('65', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.19/1.38         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 1.19/1.38      inference('sup-', [status(thm)], ['9', '11'])).
% 1.19/1.38  thf('66', plain,
% 1.19/1.38      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.19/1.38         (~ (r2_hidden @ X2 @ X0)
% 1.19/1.38          | ~ (r2_hidden @ X2 @ X3)
% 1.19/1.38          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.19/1.38      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.19/1.38  thf('67', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.19/1.38         (~ (r1_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 1.19/1.38          | ~ (r2_hidden @ X4 @ X5))),
% 1.19/1.38      inference('sup-', [status(thm)], ['65', '66'])).
% 1.19/1.38  thf('68', plain, (![X4 : $i]: ~ (r2_hidden @ X4 @ k1_xboole_0)),
% 1.19/1.38      inference('sup-', [status(thm)], ['64', '67'])).
% 1.19/1.38  thf('69', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['48', '68'])).
% 1.19/1.38  thf('70', plain,
% 1.19/1.38      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 1.19/1.38      inference('split', [status(esa)], ['21'])).
% 1.19/1.38  thf('71', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 1.19/1.38      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 1.19/1.38  thf('72', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 1.19/1.38      inference('simpl_trail', [status(thm)], ['37', '71'])).
% 1.19/1.38  thf('73', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['4', '13'])).
% 1.19/1.38  thf('74', plain,
% 1.19/1.38      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.19/1.38         (~ (r2_hidden @ X2 @ X0)
% 1.19/1.38          | ~ (r2_hidden @ X2 @ X3)
% 1.19/1.38          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.19/1.38      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.19/1.38  thf('75', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.19/1.38      inference('sup-', [status(thm)], ['73', '74'])).
% 1.19/1.38  thf('76', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 1.19/1.38      inference('sup-', [status(thm)], ['72', '75'])).
% 1.19/1.38  thf('77', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.19/1.38      inference('sup-', [status(thm)], ['50', '56'])).
% 1.19/1.38  thf('78', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 1.19/1.38      inference('demod', [status(thm)], ['76', '77'])).
% 1.19/1.38  thf('79', plain, ($false), inference('sup-', [status(thm)], ['14', '78'])).
% 1.19/1.38  
% 1.19/1.38  % SZS output end Refutation
% 1.19/1.38  
% 1.19/1.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
