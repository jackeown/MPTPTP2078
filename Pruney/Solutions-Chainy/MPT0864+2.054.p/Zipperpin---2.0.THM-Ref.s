%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tfcBP7VhPz

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:06 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 183 expanded)
%              Number of leaves         :   36 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  784 (1622 expanded)
%              Number of equality atoms :  107 ( 246 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      | ( r2_hidden @ X49 @ X56 )
      | ( X56
       != ( k4_enumset1 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( r2_hidden @ X49 @ ( k4_enumset1 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 ) )
      | ( zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X42 != X41 )
      | ~ ( zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X41: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ~ ( zip_tseitin_0 @ X41 @ X43 @ X44 @ X45 @ X46 @ X47 @ X41 ) ),
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
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X27 ) @ X29 )
      | ~ ( r2_hidden @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
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

thf('18',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('19',plain,(
    ! [X61: $i,X63: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X61 @ X63 ) )
      = X63 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('20',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['18','19'])).

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
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X37 ) @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_tarski @ ( k4_tarski @ X37 @ X38 ) @ ( k4_tarski @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ X0 ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ sk_A ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','27'])).

thf('29',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('30',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( r1_tarski @ X32 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('33',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('34',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 != X34 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X34 ) )
       != ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('35',plain,(
    ! [X34: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X34 ) )
     != ( k1_tarski @ X34 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X34: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X34 ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','39'])).

thf('41',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('43',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('44',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X61 @ X62 ) )
      = X61 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('46',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('48',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X37 ) @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_tarski @ ( k4_tarski @ X37 @ X38 ) @ ( k4_tarski @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ X0 ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
      = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','52'])).

thf('54',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('55',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('56',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( r1_tarski @ X32 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('58',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X34: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X34 ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','60'])).

thf('62',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('63',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['41','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tfcBP7VhPz
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 19:12:42 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 476 iterations in 0.131s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.58  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.40/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.40/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.40/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.40/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.58  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.40/0.58  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(t70_enumset1, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (![X7 : $i, X8 : $i]:
% 0.40/0.58         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.40/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.58  thf(t69_enumset1, axiom,
% 0.40/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.58  thf('1', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.40/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['0', '1'])).
% 0.40/0.58  thf(t71_enumset1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.58         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.40/0.58      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.40/0.58  thf(t72_enumset1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.58     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.58         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 0.40/0.58           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 0.40/0.58      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.40/0.58  thf(t73_enumset1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.40/0.58     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.40/0.58       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.58         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.40/0.58           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.40/0.58      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.40/0.58  thf(d4_enumset1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.40/0.58     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.40/0.58       ( ![H:$i]:
% 0.40/0.58         ( ( r2_hidden @ H @ G ) <=>
% 0.40/0.58           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.40/0.58                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.40/0.58  thf(zf_stmt_1, axiom,
% 0.40/0.58    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.40/0.58     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.40/0.58       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.40/0.58         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_2, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.40/0.58     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.40/0.58       ( ![H:$i]:
% 0.40/0.58         ( ( r2_hidden @ H @ G ) <=>
% 0.40/0.58           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, 
% 0.40/0.58         X56 : $i]:
% 0.40/0.58         ((zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 0.40/0.58          | (r2_hidden @ X49 @ X56)
% 0.40/0.58          | ((X56) != (k4_enumset1 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.40/0.58         ((r2_hidden @ X49 @ (k4_enumset1 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50))
% 0.40/0.58          | (zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 0.40/0.58      inference('simplify', [status(thm)], ['6'])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.58         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.40/0.58          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.40/0.58      inference('sup+', [status(thm)], ['5', '7'])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.40/0.58         (((X42) != (X41))
% 0.40/0.58          | ~ (zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X41))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X41 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.40/0.58         ~ (zip_tseitin_0 @ X41 @ X43 @ X44 @ X45 @ X46 @ X47 @ X41)),
% 0.40/0.58      inference('simplify', [status(thm)], ['9'])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.58         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.40/0.58      inference('sup-', [status(thm)], ['8', '10'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.58         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['4', '11'])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['3', '12'])).
% 0.40/0.58  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['2', '13'])).
% 0.40/0.58  thf(l1_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X27 : $i, X29 : $i]:
% 0.40/0.58         ((r1_tarski @ (k1_tarski @ X27) @ X29) | ~ (r2_hidden @ X27 @ X29))),
% 0.40/0.58      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.58  thf('17', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.40/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.58  thf(t20_mcart_1, conjecture,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.40/0.58       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_3, negated_conjecture,
% 0.40/0.58    (~( ![A:$i]:
% 0.40/0.58        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.40/0.58          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.40/0.58  thf('18', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.58  thf(t7_mcart_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.40/0.58       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X61 : $i, X63 : $i]: ((k2_mcart_1 @ (k4_tarski @ X61 @ X63)) = (X63))),
% 0.40/0.58      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.40/0.58  thf('20', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.40/0.58      inference('sup+', [status(thm)], ['18', '19'])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('split', [status(esa)], ['21'])).
% 0.40/0.58  thf('23', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['20', '22'])).
% 0.40/0.58  thf('24', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.40/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['23', '24'])).
% 0.40/0.58  thf(t36_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.40/0.58         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.40/0.58       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.40/0.58         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.40/0.58         ((k2_zfmisc_1 @ (k1_tarski @ X37) @ (k2_tarski @ X38 @ X39))
% 0.40/0.58           = (k2_tarski @ (k4_tarski @ X37 @ X38) @ (k4_tarski @ X37 @ X39)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      ((![X0 : $i]:
% 0.40/0.58          ((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_A @ X0))
% 0.40/0.58            = (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ X0))))
% 0.40/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['25', '26'])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.40/0.58          = (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ sk_A))))
% 0.40/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['17', '27'])).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.40/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['23', '24'])).
% 0.40/0.58  thf('30', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.40/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.40/0.58          = (k1_tarski @ sk_A)))
% 0.40/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.40/0.58  thf(t135_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.40/0.58         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.40/0.58       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (![X32 : $i, X33 : $i]:
% 0.40/0.58         (((X32) = (k1_xboole_0))
% 0.40/0.58          | ~ (r1_tarski @ X32 @ (k2_zfmisc_1 @ X33 @ X32)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.40/0.58         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.40/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.58  thf(t20_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.40/0.58         ( k1_tarski @ A ) ) <=>
% 0.40/0.58       ( ( A ) != ( B ) ) ))).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (![X34 : $i, X35 : $i]:
% 0.40/0.58         (((X35) != (X34))
% 0.40/0.58          | ((k4_xboole_0 @ (k1_tarski @ X35) @ (k1_tarski @ X34))
% 0.40/0.58              != (k1_tarski @ X35)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      (![X34 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X34))
% 0.40/0.58           != (k1_tarski @ X34))),
% 0.40/0.58      inference('simplify', [status(thm)], ['34'])).
% 0.40/0.58  thf(idempotence_k2_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.40/0.58  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.40/0.58  thf(t46_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (![X4 : $i, X5 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.40/0.58  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['36', '37'])).
% 0.40/0.58  thf('39', plain, (![X34 : $i]: ((k1_xboole_0) != (k1_tarski @ X34))),
% 0.40/0.58      inference('demod', [status(thm)], ['35', '38'])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.40/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('clc', [status(thm)], ['33', '39'])).
% 0.40/0.58  thf('41', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['16', '40'])).
% 0.40/0.58  thf('42', plain,
% 0.40/0.58      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.58  thf('43', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.40/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.58  thf('44', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.58  thf('45', plain,
% 0.40/0.58      (![X61 : $i, X62 : $i]: ((k1_mcart_1 @ (k4_tarski @ X61 @ X62)) = (X61))),
% 0.40/0.58      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.40/0.58  thf('46', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.40/0.58      inference('sup+', [status(thm)], ['44', '45'])).
% 0.40/0.58  thf('47', plain,
% 0.40/0.58      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('split', [status(esa)], ['21'])).
% 0.40/0.58  thf('48', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['46', '47'])).
% 0.40/0.58  thf('49', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.58  thf('50', plain,
% 0.40/0.58      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['48', '49'])).
% 0.40/0.58  thf('51', plain,
% 0.40/0.58      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.40/0.58         ((k2_zfmisc_1 @ (k1_tarski @ X37) @ (k2_tarski @ X38 @ X39))
% 0.40/0.58           = (k2_tarski @ (k4_tarski @ X37 @ X38) @ (k4_tarski @ X37 @ X39)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.40/0.58  thf('52', plain,
% 0.40/0.58      ((![X0 : $i]:
% 0.40/0.58          ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ X0))
% 0.40/0.58            = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ X0))))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.40/0.58  thf('53', plain,
% 0.40/0.58      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.40/0.58          = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ sk_C))))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['43', '52'])).
% 0.40/0.58  thf('54', plain,
% 0.40/0.58      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['48', '49'])).
% 0.40/0.58  thf('55', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.40/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.58  thf('56', plain,
% 0.40/0.58      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.40/0.58          = (k1_tarski @ sk_A)))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.40/0.58  thf('57', plain,
% 0.40/0.58      (![X32 : $i, X33 : $i]:
% 0.40/0.58         (((X32) = (k1_xboole_0))
% 0.40/0.58          | ~ (r1_tarski @ X32 @ (k2_zfmisc_1 @ X32 @ X33)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.40/0.58  thf('58', plain,
% 0.40/0.58      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.40/0.58         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.40/0.58  thf('59', plain, (![X34 : $i]: ((k1_xboole_0) != (k1_tarski @ X34))),
% 0.40/0.58      inference('demod', [status(thm)], ['35', '38'])).
% 0.40/0.58  thf('60', plain,
% 0.40/0.58      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('clc', [status(thm)], ['58', '59'])).
% 0.40/0.58  thf('61', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['42', '60'])).
% 0.40/0.58  thf('62', plain,
% 0.40/0.58      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.40/0.58      inference('split', [status(esa)], ['21'])).
% 0.40/0.58  thf('63', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.40/0.58      inference('sat_resolution*', [status(thm)], ['61', '62'])).
% 0.40/0.58  thf('64', plain, ($false),
% 0.40/0.58      inference('simpl_trail', [status(thm)], ['41', '63'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
