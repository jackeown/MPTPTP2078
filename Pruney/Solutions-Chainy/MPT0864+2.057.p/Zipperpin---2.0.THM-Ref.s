%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QPzfahYel7

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:07 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 159 expanded)
%              Number of leaves         :   40 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  697 (1302 expanded)
%              Number of equality atoms :   91 ( 174 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X10 @ X10 @ X11 @ X12 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
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

thf('6',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( zip_tseitin_0 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 )
      | ( r2_hidden @ X55 @ X62 )
      | ( X62
       != ( k4_enumset1 @ X61 @ X60 @ X59 @ X58 @ X57 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( r2_hidden @ X55 @ ( k4_enumset1 @ X61 @ X60 @ X59 @ X58 @ X57 @ X56 ) )
      | ( zip_tseitin_0 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X48 != X47 )
      | ~ ( zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X47: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ~ ( zip_tseitin_0 @ X47 @ X49 @ X50 @ X51 @ X52 @ X53 @ X47 ) ),
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

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('15',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

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

thf('17',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('18',plain,(
    ! [X67: $i,X69: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X67 @ X69 ) )
      = X69 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('19',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','21'])).

thf('23',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X45 ) @ ( k1_tarski @ X46 ) )
      = ( k1_tarski @ ( k4_tarski @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( r1_tarski @ X40 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('28',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43 != X42 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X42 ) )
       != ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('29',plain,(
    ! [X42: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X42 ) @ ( k1_tarski @ X42 ) )
     != ( k1_tarski @ X42 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('34',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X42: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X42 ) ) ),
    inference(demod,[status(thm)],['29','32','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['27','38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','39'])).

thf('41',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('43',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    ! [X67: $i,X68: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X67 @ X68 ) )
      = X67 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('45',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('47',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X45 ) @ ( k1_tarski @ X46 ) )
      = ( k1_tarski @ ( k4_tarski @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('51',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( r1_tarski @ X40 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X42: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X42 ) ) ),
    inference(demod,[status(thm)],['29','32','37'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','55'])).

thf('57',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('58',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['41','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QPzfahYel7
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 268 iterations in 0.108s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.39/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.39/0.59  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.39/0.59  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.39/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.59  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.39/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.39/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.59  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.39/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.59  thf(t70_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (![X8 : $i, X9 : $i]:
% 0.39/0.59         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 0.39/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.59  thf(t69_enumset1, axiom,
% 0.39/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.59  thf('1', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.39/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['0', '1'])).
% 0.39/0.59  thf(t71_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.59         ((k2_enumset1 @ X10 @ X10 @ X11 @ X12)
% 0.39/0.59           = (k1_enumset1 @ X10 @ X11 @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.39/0.59  thf(t72_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.59         ((k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16)
% 0.39/0.59           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.39/0.59      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.39/0.59  thf(t73_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.39/0.59     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.39/0.59       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.59         ((k4_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.39/0.59           = (k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.39/0.59      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.39/0.59  thf(d4_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.39/0.59     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.39/0.59       ( ![H:$i]:
% 0.39/0.59         ( ( r2_hidden @ H @ G ) <=>
% 0.39/0.59           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.39/0.59                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.39/0.59  thf(zf_stmt_1, axiom,
% 0.39/0.59    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.39/0.59     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.39/0.59       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.39/0.59         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_2, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.39/0.59     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.39/0.59       ( ![H:$i]:
% 0.39/0.59         ( ( r2_hidden @ H @ G ) <=>
% 0.39/0.59           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i, 
% 0.39/0.59         X62 : $i]:
% 0.39/0.59         ((zip_tseitin_0 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61)
% 0.39/0.59          | (r2_hidden @ X55 @ X62)
% 0.39/0.59          | ((X62) != (k4_enumset1 @ X61 @ X60 @ X59 @ X58 @ X57 @ X56)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 0.39/0.59         ((r2_hidden @ X55 @ (k4_enumset1 @ X61 @ X60 @ X59 @ X58 @ X57 @ X56))
% 0.39/0.59          | (zip_tseitin_0 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61))),
% 0.39/0.59      inference('simplify', [status(thm)], ['6'])).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.59         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.59          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.39/0.59      inference('sup+', [status(thm)], ['5', '7'])).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.39/0.59         (((X48) != (X47))
% 0.39/0.59          | ~ (zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X47))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (![X47 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.39/0.59         ~ (zip_tseitin_0 @ X47 @ X49 @ X50 @ X51 @ X52 @ X53 @ X47)),
% 0.39/0.59      inference('simplify', [status(thm)], ['9'])).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.59         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '10'])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['4', '11'])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['3', '12'])).
% 0.39/0.59  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['2', '13'])).
% 0.39/0.59  thf(l1_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      (![X35 : $i, X37 : $i]:
% 0.39/0.59         ((r1_tarski @ (k1_tarski @ X35) @ X37) | ~ (r2_hidden @ X35 @ X37))),
% 0.39/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.59  thf(t20_mcart_1, conjecture,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.39/0.59       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_3, negated_conjecture,
% 0.39/0.59    (~( ![A:$i]:
% 0.39/0.59        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.39/0.59          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.39/0.59  thf('17', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf(t7_mcart_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.39/0.59       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      (![X67 : $i, X69 : $i]: ((k2_mcart_1 @ (k4_tarski @ X67 @ X69)) = (X69))),
% 0.39/0.59      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.39/0.59  thf('19', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.39/0.59      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.39/0.59      inference('split', [status(esa)], ['20'])).
% 0.39/0.59  thf('22', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['19', '21'])).
% 0.39/0.59  thf('23', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.39/0.59         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['22', '23'])).
% 0.39/0.59  thf(t35_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.39/0.59       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X45 : $i, X46 : $i]:
% 0.39/0.59         ((k2_zfmisc_1 @ (k1_tarski @ X45) @ (k1_tarski @ X46))
% 0.39/0.59           = (k1_tarski @ (k4_tarski @ X45 @ X46)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.39/0.59  thf(t135_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.39/0.59         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.39/0.59       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      (![X40 : $i, X41 : $i]:
% 0.39/0.59         (((X40) = (k1_xboole_0))
% 0.39/0.59          | ~ (r1_tarski @ X40 @ (k2_zfmisc_1 @ X41 @ X40)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.39/0.59          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.59  thf(t20_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.39/0.59         ( k1_tarski @ A ) ) <=>
% 0.39/0.59       ( ( A ) != ( B ) ) ))).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      (![X42 : $i, X43 : $i]:
% 0.39/0.59         (((X43) != (X42))
% 0.39/0.59          | ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X42))
% 0.39/0.59              != (k1_tarski @ X43)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      (![X42 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k1_tarski @ X42) @ (k1_tarski @ X42))
% 0.39/0.59           != (k1_tarski @ X42))),
% 0.39/0.59      inference('simplify', [status(thm)], ['28'])).
% 0.39/0.59  thf(idempotence_k3_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.39/0.59  thf('30', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.39/0.59      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.39/0.59  thf(t100_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      (![X1 : $i, X2 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ X1 @ X2)
% 0.39/0.59           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['30', '31'])).
% 0.39/0.59  thf(t21_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      (![X3 : $i, X4 : $i]:
% 0.39/0.59         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (X3))),
% 0.39/0.59      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (![X1 : $i, X2 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ X1 @ X2)
% 0.39/0.59           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.39/0.59           = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['33', '34'])).
% 0.39/0.59  thf(t46_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.39/0.59  thf('36', plain,
% 0.39/0.59      (![X5 : $i, X6 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.39/0.59      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.39/0.59  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['35', '36'])).
% 0.39/0.59  thf('38', plain, (![X42 : $i]: ((k1_xboole_0) != (k1_tarski @ X42))),
% 0.39/0.59      inference('demod', [status(thm)], ['29', '32', '37'])).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.39/0.59      inference('clc', [status(thm)], ['27', '38'])).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.39/0.59         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['24', '39'])).
% 0.39/0.59  thf('41', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['16', '40'])).
% 0.39/0.59  thf('42', plain,
% 0.39/0.59      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.59  thf('43', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('44', plain,
% 0.39/0.59      (![X67 : $i, X68 : $i]: ((k1_mcart_1 @ (k4_tarski @ X67 @ X68)) = (X67))),
% 0.39/0.59      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.39/0.59  thf('45', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['43', '44'])).
% 0.39/0.59  thf('46', plain,
% 0.39/0.59      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.39/0.59      inference('split', [status(esa)], ['20'])).
% 0.39/0.59  thf('47', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['45', '46'])).
% 0.39/0.59  thf('48', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('49', plain,
% 0.39/0.59      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.39/0.59         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['47', '48'])).
% 0.39/0.59  thf('50', plain,
% 0.39/0.59      (![X45 : $i, X46 : $i]:
% 0.39/0.59         ((k2_zfmisc_1 @ (k1_tarski @ X45) @ (k1_tarski @ X46))
% 0.39/0.59           = (k1_tarski @ (k4_tarski @ X45 @ X46)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.39/0.59  thf('51', plain,
% 0.39/0.59      (![X40 : $i, X41 : $i]:
% 0.39/0.59         (((X40) = (k1_xboole_0))
% 0.39/0.59          | ~ (r1_tarski @ X40 @ (k2_zfmisc_1 @ X40 @ X41)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.39/0.59  thf('52', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.39/0.59          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.39/0.59  thf('53', plain, (![X42 : $i]: ((k1_xboole_0) != (k1_tarski @ X42))),
% 0.39/0.59      inference('demod', [status(thm)], ['29', '32', '37'])).
% 0.39/0.59  thf('54', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.39/0.59      inference('clc', [status(thm)], ['52', '53'])).
% 0.39/0.59  thf('55', plain,
% 0.39/0.59      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.39/0.59         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['49', '54'])).
% 0.39/0.59  thf('56', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['42', '55'])).
% 0.39/0.59  thf('57', plain,
% 0.39/0.59      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.39/0.59      inference('split', [status(esa)], ['20'])).
% 0.39/0.59  thf('58', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.39/0.59  thf('59', plain, ($false),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['41', '58'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
