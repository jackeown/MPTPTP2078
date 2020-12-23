%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jYTjY8M8rZ

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:07 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 201 expanded)
%              Number of leaves         :   40 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  841 (1754 expanded)
%              Number of equality atoms :  114 ( 262 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('1',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('2',plain,(
    ! [X69: $i,X71: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X69 @ X71 ) )
      = X71 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('3',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('9',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X45 ) @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_tarski @ ( k4_tarski @ X45 @ X46 ) @ ( k4_tarski @ X45 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ X0 ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ sk_A ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','10'])).

thf('12',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( r1_tarski @ X40 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('16',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('17',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43 != X42 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X42 ) )
       != ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('18',plain,(
    ! [X42: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X42 ) @ ( k1_tarski @ X42 ) )
     != ( k1_tarski @ X42 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X42: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X42 ) ) ),
    inference(demod,[status(thm)],['18','21','26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','27'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('30',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X10 @ X10 @ X11 @ X12 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k4_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [H: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A )
    <=> ( ( H != A )
        & ( H != B )
        & ( H != C )
        & ( H != D )
        & ( H != E )
        & ( H != F ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i,X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ( zip_tseitin_0 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 )
      | ( r2_hidden @ X57 @ X64 )
      | ( X64
       != ( k4_enumset1 @ X63 @ X62 @ X61 @ X60 @ X59 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( r2_hidden @ X57 @ ( k4_enumset1 @ X63 @ X62 @ X61 @ X60 @ X59 @ X58 ) )
      | ( zip_tseitin_0 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( X50 != X49 )
      | ~ ( zip_tseitin_0 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('39',plain,(
    ! [X49: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ~ ( zip_tseitin_0 @ X49 @ X51 @ X52 @ X53 @ X54 @ X55 @ X49 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','42'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('44',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('48',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('49',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X69: $i,X70: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X69 @ X70 ) )
      = X69 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('51',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('53',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X45 ) @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_tarski @ ( k4_tarski @ X45 @ X46 ) @ ( k4_tarski @ X45 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ X0 ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
      = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','57'])).

thf('59',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('60',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('61',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( r1_tarski @ X40 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('63',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X42: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X42 ) ) ),
    inference(demod,[status(thm)],['18','21','26'])).

thf('65',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','65'])).

thf('67',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('68',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['46','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jYTjY8M8rZ
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 568 iterations in 0.235s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.68  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.45/0.68  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.45/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.68  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.68  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.68  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.45/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.68  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.68  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.68  thf(t69_enumset1, axiom,
% 0.45/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.68  thf('0', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf(t20_mcart_1, conjecture,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.45/0.68       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i]:
% 0.45/0.68        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.45/0.68          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.45/0.68  thf('1', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(t7_mcart_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.45/0.68       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      (![X69 : $i, X71 : $i]: ((k2_mcart_1 @ (k4_tarski @ X69 @ X71)) = (X71))),
% 0.45/0.68      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.45/0.68  thf('3', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.45/0.68      inference('sup+', [status(thm)], ['1', '2'])).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('5', plain,
% 0.45/0.68      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('split', [status(esa)], ['4'])).
% 0.45/0.68  thf('6', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['3', '5'])).
% 0.45/0.68  thf('7', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.45/0.68         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.45/0.68  thf(t36_zfmisc_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.45/0.68         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.45/0.68       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.45/0.68         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.45/0.68  thf('9', plain,
% 0.45/0.68      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.45/0.68         ((k2_zfmisc_1 @ (k1_tarski @ X45) @ (k2_tarski @ X46 @ X47))
% 0.45/0.68           = (k2_tarski @ (k4_tarski @ X45 @ X46) @ (k4_tarski @ X45 @ X47)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.45/0.68  thf('10', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          ((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_A @ X0))
% 0.45/0.68            = (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ X0))))
% 0.45/0.68         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.45/0.68          = (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ sk_A))))
% 0.45/0.68         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['0', '10'])).
% 0.45/0.68  thf('12', plain,
% 0.45/0.68      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.45/0.68         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.45/0.68  thf('13', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.45/0.68          = (k1_tarski @ sk_A)))
% 0.45/0.68         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.45/0.68  thf(t135_zfmisc_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.45/0.68         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.45/0.68       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      (![X40 : $i, X41 : $i]:
% 0.45/0.68         (((X40) = (k1_xboole_0))
% 0.45/0.68          | ~ (r1_tarski @ X40 @ (k2_zfmisc_1 @ X41 @ X40)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.45/0.68  thf('16', plain,
% 0.45/0.68      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.45/0.68         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.45/0.68         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.68  thf(t20_zfmisc_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.45/0.68         ( k1_tarski @ A ) ) <=>
% 0.45/0.68       ( ( A ) != ( B ) ) ))).
% 0.45/0.68  thf('17', plain,
% 0.45/0.68      (![X42 : $i, X43 : $i]:
% 0.45/0.68         (((X43) != (X42))
% 0.45/0.68          | ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X42))
% 0.45/0.68              != (k1_tarski @ X43)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.45/0.68  thf('18', plain,
% 0.45/0.68      (![X42 : $i]:
% 0.45/0.68         ((k4_xboole_0 @ (k1_tarski @ X42) @ (k1_tarski @ X42))
% 0.45/0.68           != (k1_tarski @ X42))),
% 0.45/0.68      inference('simplify', [status(thm)], ['17'])).
% 0.45/0.68  thf(idempotence_k3_xboole_0, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.68  thf('19', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.68      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.68  thf(t100_xboole_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.68  thf('20', plain,
% 0.45/0.68      (![X1 : $i, X2 : $i]:
% 0.45/0.68         ((k4_xboole_0 @ X1 @ X2)
% 0.45/0.68           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.68  thf('21', plain,
% 0.45/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['19', '20'])).
% 0.45/0.68  thf(t21_xboole_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.45/0.68  thf('22', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i]:
% 0.45/0.68         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (X3))),
% 0.45/0.68      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.45/0.68  thf('23', plain,
% 0.45/0.68      (![X1 : $i, X2 : $i]:
% 0.45/0.68         ((k4_xboole_0 @ X1 @ X2)
% 0.45/0.68           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.68  thf('24', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.45/0.68           = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['22', '23'])).
% 0.45/0.68  thf(t46_xboole_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.45/0.68  thf('25', plain,
% 0.45/0.68      (![X5 : $i, X6 : $i]:
% 0.45/0.68         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.45/0.68  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['24', '25'])).
% 0.45/0.68  thf('27', plain, (![X42 : $i]: ((k1_xboole_0) != (k1_tarski @ X42))),
% 0.45/0.68      inference('demod', [status(thm)], ['18', '21', '26'])).
% 0.45/0.68  thf('28', plain,
% 0.45/0.68      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.45/0.68         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('clc', [status(thm)], ['16', '27'])).
% 0.45/0.68  thf(t70_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.68  thf('29', plain,
% 0.45/0.68      (![X8 : $i, X9 : $i]:
% 0.45/0.68         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 0.45/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.68  thf('30', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf('31', plain,
% 0.45/0.68      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['29', '30'])).
% 0.45/0.68  thf(t71_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.68  thf('32', plain,
% 0.45/0.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.68         ((k2_enumset1 @ X10 @ X10 @ X11 @ X12)
% 0.45/0.68           = (k1_enumset1 @ X10 @ X11 @ X12))),
% 0.45/0.68      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.68  thf(t72_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.68         ((k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16)
% 0.45/0.68           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.45/0.68      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.45/0.68  thf(t73_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.68     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.45/0.68       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.45/0.68  thf('34', plain,
% 0.45/0.68      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.68         ((k4_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.45/0.68           = (k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.45/0.68  thf(d4_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.45/0.68     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.45/0.68       ( ![H:$i]:
% 0.45/0.68         ( ( r2_hidden @ H @ G ) <=>
% 0.45/0.68           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.45/0.68                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.45/0.68  thf(zf_stmt_2, axiom,
% 0.45/0.68    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.45/0.68     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.45/0.68       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.45/0.68         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_3, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.45/0.68     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.45/0.68       ( ![H:$i]:
% 0.45/0.68         ( ( r2_hidden @ H @ G ) <=>
% 0.45/0.68           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.45/0.68  thf('35', plain,
% 0.45/0.68      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i, 
% 0.45/0.68         X64 : $i]:
% 0.45/0.68         ((zip_tseitin_0 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63)
% 0.45/0.68          | (r2_hidden @ X57 @ X64)
% 0.45/0.68          | ((X64) != (k4_enumset1 @ X63 @ X62 @ X61 @ X60 @ X59 @ X58)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.68  thf('36', plain,
% 0.45/0.68      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 0.45/0.68         ((r2_hidden @ X57 @ (k4_enumset1 @ X63 @ X62 @ X61 @ X60 @ X59 @ X58))
% 0.45/0.68          | (zip_tseitin_0 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63))),
% 0.45/0.68      inference('simplify', [status(thm)], ['35'])).
% 0.45/0.68  thf('37', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.68         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.45/0.68          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.45/0.68      inference('sup+', [status(thm)], ['34', '36'])).
% 0.45/0.68  thf('38', plain,
% 0.45/0.68      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.45/0.68         (((X50) != (X49))
% 0.45/0.68          | ~ (zip_tseitin_0 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X49))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.68  thf('39', plain,
% 0.45/0.68      (![X49 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.45/0.68         ~ (zip_tseitin_0 @ X49 @ X51 @ X52 @ X53 @ X54 @ X55 @ X49)),
% 0.45/0.68      inference('simplify', [status(thm)], ['38'])).
% 0.45/0.68  thf('40', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.68         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.45/0.68      inference('sup-', [status(thm)], ['37', '39'])).
% 0.45/0.68  thf('41', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.68         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['33', '40'])).
% 0.45/0.68  thf('42', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['32', '41'])).
% 0.45/0.68  thf('43', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['31', '42'])).
% 0.45/0.68  thf(l1_zfmisc_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.45/0.68  thf('44', plain,
% 0.45/0.68      (![X35 : $i, X37 : $i]:
% 0.45/0.68         ((r1_tarski @ (k1_tarski @ X35) @ X37) | ~ (r2_hidden @ X35 @ X37))),
% 0.45/0.68      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.45/0.68  thf('45', plain,
% 0.45/0.68      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.68  thf('46', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['28', '45'])).
% 0.45/0.68  thf('47', plain,
% 0.45/0.68      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.68  thf('48', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf('49', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('50', plain,
% 0.45/0.68      (![X69 : $i, X70 : $i]: ((k1_mcart_1 @ (k4_tarski @ X69 @ X70)) = (X69))),
% 0.45/0.68      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.45/0.68  thf('51', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['49', '50'])).
% 0.45/0.68  thf('52', plain,
% 0.45/0.68      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('split', [status(esa)], ['4'])).
% 0.45/0.68  thf('53', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['51', '52'])).
% 0.45/0.68  thf('54', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('55', plain,
% 0.45/0.68      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.45/0.68         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['53', '54'])).
% 0.45/0.68  thf('56', plain,
% 0.45/0.68      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.45/0.68         ((k2_zfmisc_1 @ (k1_tarski @ X45) @ (k2_tarski @ X46 @ X47))
% 0.45/0.68           = (k2_tarski @ (k4_tarski @ X45 @ X46) @ (k4_tarski @ X45 @ X47)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.45/0.68  thf('57', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ X0))
% 0.45/0.68            = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ X0))))
% 0.45/0.68         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['55', '56'])).
% 0.45/0.68  thf('58', plain,
% 0.45/0.68      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.45/0.68          = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ sk_C))))
% 0.45/0.68         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['48', '57'])).
% 0.45/0.68  thf('59', plain,
% 0.45/0.68      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.45/0.68         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['53', '54'])).
% 0.45/0.68  thf('60', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf('61', plain,
% 0.45/0.68      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.45/0.68          = (k1_tarski @ sk_A)))
% 0.45/0.68         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.45/0.68  thf('62', plain,
% 0.45/0.68      (![X40 : $i, X41 : $i]:
% 0.45/0.68         (((X40) = (k1_xboole_0))
% 0.45/0.68          | ~ (r1_tarski @ X40 @ (k2_zfmisc_1 @ X40 @ X41)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.45/0.68  thf('63', plain,
% 0.45/0.68      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.45/0.68         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.45/0.68         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['61', '62'])).
% 0.45/0.68  thf('64', plain, (![X42 : $i]: ((k1_xboole_0) != (k1_tarski @ X42))),
% 0.45/0.68      inference('demod', [status(thm)], ['18', '21', '26'])).
% 0.45/0.68  thf('65', plain,
% 0.45/0.68      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.45/0.68         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.68      inference('clc', [status(thm)], ['63', '64'])).
% 0.45/0.68  thf('66', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['47', '65'])).
% 0.45/0.68  thf('67', plain,
% 0.45/0.68      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.45/0.68      inference('split', [status(esa)], ['4'])).
% 0.45/0.68  thf('68', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['66', '67'])).
% 0.45/0.68  thf('69', plain, ($false),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['46', '68'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.51/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
