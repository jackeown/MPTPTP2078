%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U96HsrZfwB

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:08 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 190 expanded)
%              Number of leaves         :   38 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  814 (1674 expanded)
%              Number of equality atoms :  110 ( 252 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
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
    ! [X64: $i,X66: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X64 @ X66 ) )
      = X66 ) ),
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
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X40 ) @ ( k2_tarski @ X41 @ X42 ) )
      = ( k2_tarski @ ( k4_tarski @ X40 @ X41 ) @ ( k4_tarski @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ X0 ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ X0 ) @ ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ X0 ) ) )
        | ( ( k2_tarski @ sk_A @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ sk_A ) ) )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('18',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38 != X37 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X37 ) )
       != ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('19',plain,(
    ! [X37: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X37 ) )
     != ( k1_tarski @ X37 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('24',plain,(
    ! [X37: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X37 ) ) ),
    inference(demod,[status(thm)],['19','22','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','24'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('27',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
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

thf('32',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( zip_tseitin_0 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 )
      | ( r2_hidden @ X52 @ X59 )
      | ( X59
       != ( k4_enumset1 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( r2_hidden @ X52 @ ( k4_enumset1 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53 ) )
      | ( zip_tseitin_0 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X45 != X44 )
      | ~ ( zip_tseitin_0 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    ! [X44: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ~ ( zip_tseitin_0 @ X44 @ X46 @ X47 @ X48 @ X49 @ X50 @ X44 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','39'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('41',plain,(
    ! [X32: $i,X34: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X32 ) @ X34 )
      | ~ ( r2_hidden @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X64 @ X65 ) )
      = X64 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('48',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('50',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X40 ) @ ( k2_tarski @ X41 @ X42 ) )
      = ( k2_tarski @ ( k4_tarski @ X40 @ X41 ) @ ( k4_tarski @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ X0 ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
      = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','54'])).

thf('56',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('57',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('58',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('60',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X37: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X37 ) ) ),
    inference(demod,[status(thm)],['19','22','23'])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','62'])).

thf('64',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('65',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['43','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U96HsrZfwB
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:55:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 645 iterations in 0.244s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.70  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.70  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.46/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.70  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.46/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.70  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.46/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.46/0.70  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.70  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.70  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.70  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(t69_enumset1, axiom,
% 0.46/0.70    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.70  thf('0', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.70  thf(t20_mcart_1, conjecture,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.46/0.70       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i]:
% 0.46/0.70        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.46/0.70          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.46/0.70  thf('1', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(t7_mcart_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.46/0.70       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      (![X64 : $i, X66 : $i]: ((k2_mcart_1 @ (k4_tarski @ X64 @ X66)) = (X66))),
% 0.46/0.70      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.46/0.70  thf('3', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.46/0.70      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('split', [status(esa)], ['4'])).
% 0.46/0.70  thf('6', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['3', '5'])).
% 0.46/0.70  thf('7', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('8', plain,
% 0.46/0.70      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.46/0.70         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.70  thf(t36_zfmisc_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.46/0.70         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.46/0.70       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.46/0.70         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.46/0.70  thf('9', plain,
% 0.46/0.70      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.70         ((k2_zfmisc_1 @ (k1_tarski @ X40) @ (k2_tarski @ X41 @ X42))
% 0.46/0.70           = (k2_tarski @ (k4_tarski @ X40 @ X41) @ (k4_tarski @ X40 @ X42)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      ((![X0 : $i]:
% 0.46/0.70          ((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_A @ X0))
% 0.46/0.70            = (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ X0))))
% 0.46/0.70         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf(t135_zfmisc_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.46/0.70         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.46/0.70       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      (![X35 : $i, X36 : $i]:
% 0.46/0.70         (((X35) = (k1_xboole_0))
% 0.46/0.70          | ~ (r1_tarski @ X35 @ (k2_zfmisc_1 @ X36 @ X35)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      ((![X0 : $i]:
% 0.46/0.70          (~ (r1_tarski @ (k2_tarski @ sk_A @ X0) @ 
% 0.46/0.70              (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ X0)))
% 0.46/0.70           | ((k2_tarski @ sk_A @ X0) = (k1_xboole_0))))
% 0.46/0.70         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.70  thf('13', plain,
% 0.46/0.70      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.46/0.70            (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ sk_A)))
% 0.46/0.70         | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))))
% 0.46/0.70         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['0', '12'])).
% 0.46/0.70  thf('14', plain,
% 0.46/0.70      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.46/0.70         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.70  thf('15', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.70  thf('16', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.46/0.70         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.46/0.70         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.46/0.70  thf(t20_zfmisc_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.46/0.70         ( k1_tarski @ A ) ) <=>
% 0.46/0.70       ( ( A ) != ( B ) ) ))).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      (![X37 : $i, X38 : $i]:
% 0.46/0.70         (((X38) != (X37))
% 0.46/0.70          | ((k4_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X37))
% 0.46/0.70              != (k1_tarski @ X38)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      (![X37 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X37))
% 0.46/0.70           != (k1_tarski @ X37))),
% 0.46/0.70      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.70  thf(idempotence_k3_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.70  thf('20', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.70      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.46/0.70  thf(t100_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.70  thf('21', plain,
% 0.46/0.70      (![X1 : $i, X2 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X1 @ X2)
% 0.46/0.70           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.70  thf('22', plain,
% 0.46/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['20', '21'])).
% 0.46/0.70  thf(t92_xboole_1, axiom,
% 0.46/0.70    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.70  thf('23', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.70  thf('24', plain, (![X37 : $i]: ((k1_xboole_0) != (k1_tarski @ X37))),
% 0.46/0.70      inference('demod', [status(thm)], ['19', '22', '23'])).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.46/0.70         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('clc', [status(thm)], ['17', '24'])).
% 0.46/0.70  thf(t70_enumset1, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.70  thf('26', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i]:
% 0.46/0.70         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.70  thf('27', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.70  thf('28', plain,
% 0.46/0.70      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf(t71_enumset1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.70         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.46/0.70      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.46/0.70  thf(t72_enumset1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.70     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.70         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.46/0.70           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.46/0.70      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.46/0.70  thf(t73_enumset1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.70     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.46/0.70       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.46/0.70  thf('31', plain,
% 0.46/0.70      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.70         ((k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.46/0.70           = (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.46/0.70      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.46/0.70  thf(d4_enumset1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.46/0.70     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.46/0.70       ( ![H:$i]:
% 0.46/0.70         ( ( r2_hidden @ H @ G ) <=>
% 0.46/0.70           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.46/0.70                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.46/0.70  thf(zf_stmt_2, axiom,
% 0.46/0.70    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.46/0.70     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.46/0.70       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.46/0.70         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_3, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.46/0.70     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.46/0.70       ( ![H:$i]:
% 0.46/0.70         ( ( r2_hidden @ H @ G ) <=>
% 0.46/0.70           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, 
% 0.46/0.70         X59 : $i]:
% 0.46/0.70         ((zip_tseitin_0 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58)
% 0.46/0.70          | (r2_hidden @ X52 @ X59)
% 0.46/0.70          | ((X59) != (k4_enumset1 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.70  thf('33', plain,
% 0.46/0.70      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.46/0.70         ((r2_hidden @ X52 @ (k4_enumset1 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53))
% 0.46/0.70          | (zip_tseitin_0 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58))),
% 0.46/0.70      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.70         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.46/0.70          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.46/0.70      inference('sup+', [status(thm)], ['31', '33'])).
% 0.46/0.70  thf('35', plain,
% 0.46/0.70      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.46/0.70         (((X45) != (X44))
% 0.46/0.70          | ~ (zip_tseitin_0 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X44))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.70  thf('36', plain,
% 0.46/0.70      (![X44 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.46/0.70         ~ (zip_tseitin_0 @ X44 @ X46 @ X47 @ X48 @ X49 @ X50 @ X44)),
% 0.46/0.70      inference('simplify', [status(thm)], ['35'])).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.70         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.46/0.70      inference('sup-', [status(thm)], ['34', '36'])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.70         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['30', '37'])).
% 0.46/0.70  thf('39', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['29', '38'])).
% 0.46/0.70  thf('40', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['28', '39'])).
% 0.46/0.70  thf(l1_zfmisc_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.46/0.70  thf('41', plain,
% 0.46/0.70      (![X32 : $i, X34 : $i]:
% 0.46/0.70         ((r1_tarski @ (k1_tarski @ X32) @ X34) | ~ (r2_hidden @ X32 @ X34))),
% 0.46/0.70      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.46/0.70  thf('42', plain,
% 0.46/0.70      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.70  thf('43', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('demod', [status(thm)], ['25', '42'])).
% 0.46/0.70  thf('44', plain,
% 0.46/0.70      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.70  thf('45', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.70  thf('46', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('47', plain,
% 0.46/0.70      (![X64 : $i, X65 : $i]: ((k1_mcart_1 @ (k4_tarski @ X64 @ X65)) = (X64))),
% 0.46/0.70      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.46/0.70  thf('48', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['46', '47'])).
% 0.46/0.70  thf('49', plain,
% 0.46/0.70      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('split', [status(esa)], ['4'])).
% 0.46/0.70  thf('50', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['48', '49'])).
% 0.46/0.70  thf('51', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('52', plain,
% 0.46/0.70      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.46/0.70         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.70  thf('53', plain,
% 0.46/0.70      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.70         ((k2_zfmisc_1 @ (k1_tarski @ X40) @ (k2_tarski @ X41 @ X42))
% 0.46/0.70           = (k2_tarski @ (k4_tarski @ X40 @ X41) @ (k4_tarski @ X40 @ X42)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.46/0.70  thf('54', plain,
% 0.46/0.70      ((![X0 : $i]:
% 0.46/0.70          ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ X0))
% 0.46/0.70            = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ X0))))
% 0.46/0.70         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.46/0.70          = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ sk_C))))
% 0.46/0.70         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['45', '54'])).
% 0.46/0.70  thf('56', plain,
% 0.46/0.70      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.46/0.70         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.70  thf('57', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.70  thf('58', plain,
% 0.46/0.70      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.46/0.70          = (k1_tarski @ sk_A)))
% 0.46/0.70         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.46/0.70  thf('59', plain,
% 0.46/0.70      (![X35 : $i, X36 : $i]:
% 0.46/0.70         (((X35) = (k1_xboole_0))
% 0.46/0.70          | ~ (r1_tarski @ X35 @ (k2_zfmisc_1 @ X35 @ X36)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.46/0.70  thf('60', plain,
% 0.46/0.70      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.46/0.70         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.46/0.70         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.70  thf('61', plain, (![X37 : $i]: ((k1_xboole_0) != (k1_tarski @ X37))),
% 0.46/0.70      inference('demod', [status(thm)], ['19', '22', '23'])).
% 0.46/0.70  thf('62', plain,
% 0.46/0.70      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.46/0.70         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.70      inference('clc', [status(thm)], ['60', '61'])).
% 0.46/0.70  thf('63', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['44', '62'])).
% 0.46/0.70  thf('64', plain,
% 0.46/0.70      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.46/0.70      inference('split', [status(esa)], ['4'])).
% 0.46/0.70  thf('65', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.46/0.70      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 0.46/0.70  thf('66', plain, ($false),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['43', '65'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.57/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
