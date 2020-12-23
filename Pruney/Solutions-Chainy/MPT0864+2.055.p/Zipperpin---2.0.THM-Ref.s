%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n1Ur57JU3s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:07 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 207 expanded)
%              Number of leaves         :   40 (  78 expanded)
%              Depth                    :   20
%              Number of atoms          :  735 (1856 expanded)
%              Number of equality atoms :   92 ( 214 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

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

thf('0',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('1',plain,(
    ! [X70: $i,X72: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X70 @ X72 ) )
      = X72 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('2',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X10 @ X10 @ X11 @ X12 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('13',plain,(
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

thf('14',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ( zip_tseitin_0 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64 )
      | ( r2_hidden @ X58 @ X65 )
      | ( X65
       != ( k4_enumset1 @ X64 @ X63 @ X62 @ X61 @ X60 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ( r2_hidden @ X58 @ ( k4_enumset1 @ X64 @ X63 @ X62 @ X61 @ X60 @ X59 ) )
      | ( zip_tseitin_0 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( X51 != X50 )
      | ~ ( zip_tseitin_0 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    ! [X50: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ~ ( zip_tseitin_0 @ X50 @ X52 @ X53 @ X54 @ X55 @ X56 @ X50 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','21'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('24',plain,(
    ! [X40: $i,X41: $i,X42: $i,X44: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X40 @ X42 ) @ ( k2_zfmisc_1 @ X41 @ X44 ) )
      | ~ ( r2_hidden @ X42 @ X44 )
      | ~ ( r2_hidden @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','26'])).

thf('28',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X70: $i,X71: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X70 @ X71 ) )
      = X70 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('30',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('37',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('38',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('39',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( r1_tarski @ X45 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('40',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('41',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X48 != X47 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X48 ) @ ( k1_tarski @ X47 ) )
       != ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('42',plain,(
    ! [X47: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X47 ) @ ( k1_tarski @ X47 ) )
     != ( k1_tarski @ X47 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('47',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X47: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X47 ) ) ),
    inference(demod,[status(thm)],['42','45','50'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('53',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('55',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['53','54'])).

thf('56',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['27','55'])).

thf('57',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('58',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( r1_tarski @ X45 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('60',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X47: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X47 ) ) ),
    inference(demod,[status(thm)],['42','45','50'])).

thf('62',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(simplify,[status(thm)],['62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n1Ur57JU3s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:43:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 449 iterations in 0.170s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.61  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.42/0.61  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.42/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.42/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.61  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.61  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.42/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(t20_mcart_1, conjecture,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.42/0.61       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i]:
% 0.42/0.61        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.42/0.61          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.42/0.61  thf('0', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(t7_mcart_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.42/0.61       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      (![X70 : $i, X72 : $i]: ((k2_mcart_1 @ (k4_tarski @ X70 @ X72)) = (X72))),
% 0.42/0.61      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.42/0.61  thf('2', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.42/0.61      inference('sup+', [status(thm)], ['0', '1'])).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.42/0.61      inference('split', [status(esa)], ['3'])).
% 0.42/0.61  thf('5', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.42/0.61      inference('sup+', [status(thm)], ['2', '4'])).
% 0.42/0.61  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.42/0.61         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.42/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.42/0.61  thf(t70_enumset1, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X8 : $i, X9 : $i]:
% 0.42/0.61         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 0.42/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.61  thf(t69_enumset1, axiom,
% 0.42/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.61  thf('9', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.42/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['8', '9'])).
% 0.42/0.61  thf(t71_enumset1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.61         ((k2_enumset1 @ X10 @ X10 @ X11 @ X12)
% 0.42/0.61           = (k1_enumset1 @ X10 @ X11 @ X12))),
% 0.42/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.42/0.61  thf(t72_enumset1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.42/0.61         ((k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16)
% 0.42/0.61           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.42/0.61      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.42/0.61  thf(t73_enumset1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.42/0.61     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.42/0.61       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.42/0.61         ((k4_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.42/0.61           = (k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.42/0.61      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.42/0.61  thf(d4_enumset1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.42/0.61     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.42/0.61       ( ![H:$i]:
% 0.42/0.61         ( ( r2_hidden @ H @ G ) <=>
% 0.42/0.61           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.42/0.61                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.42/0.61  thf(zf_stmt_2, axiom,
% 0.42/0.61    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.42/0.61     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.42/0.61       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.42/0.61         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_3, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.42/0.61     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.42/0.61       ( ![H:$i]:
% 0.42/0.61         ( ( r2_hidden @ H @ G ) <=>
% 0.42/0.61           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i, 
% 0.42/0.61         X65 : $i]:
% 0.42/0.61         ((zip_tseitin_0 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64)
% 0.42/0.61          | (r2_hidden @ X58 @ X65)
% 0.42/0.61          | ((X65) != (k4_enumset1 @ X64 @ X63 @ X62 @ X61 @ X60 @ X59)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.61  thf('15', plain,
% 0.42/0.61      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 0.42/0.61         ((r2_hidden @ X58 @ (k4_enumset1 @ X64 @ X63 @ X62 @ X61 @ X60 @ X59))
% 0.42/0.61          | (zip_tseitin_0 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64))),
% 0.42/0.61      inference('simplify', [status(thm)], ['14'])).
% 0.42/0.61  thf('16', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.61         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.42/0.61          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.42/0.61      inference('sup+', [status(thm)], ['13', '15'])).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.42/0.61         (((X51) != (X50))
% 0.42/0.61          | ~ (zip_tseitin_0 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X50))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      (![X50 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.42/0.61         ~ (zip_tseitin_0 @ X50 @ X52 @ X53 @ X54 @ X55 @ X56 @ X50)),
% 0.42/0.61      inference('simplify', [status(thm)], ['17'])).
% 0.42/0.61  thf('19', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.61         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.42/0.61      inference('sup-', [status(thm)], ['16', '18'])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.61         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['12', '19'])).
% 0.42/0.61  thf('21', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['11', '20'])).
% 0.42/0.61  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['10', '21'])).
% 0.42/0.61  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['10', '21'])).
% 0.42/0.61  thf(l54_zfmisc_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.42/0.61       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      (![X40 : $i, X41 : $i, X42 : $i, X44 : $i]:
% 0.42/0.61         ((r2_hidden @ (k4_tarski @ X40 @ X42) @ (k2_zfmisc_1 @ X41 @ X44))
% 0.42/0.61          | ~ (r2_hidden @ X42 @ X44)
% 0.42/0.61          | ~ (r2_hidden @ X40 @ X41))),
% 0.42/0.61      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.42/0.61  thf('25', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X2 @ X1)
% 0.42/0.61          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.42/0.61             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['22', '25'])).
% 0.42/0.61  thf('27', plain,
% 0.42/0.61      (((r2_hidden @ sk_A @ 
% 0.42/0.61         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))
% 0.42/0.61         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.42/0.61      inference('sup+', [status(thm)], ['7', '26'])).
% 0.42/0.61  thf('28', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('29', plain,
% 0.42/0.61      (![X70 : $i, X71 : $i]: ((k1_mcart_1 @ (k4_tarski @ X70 @ X71)) = (X70))),
% 0.42/0.61      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.42/0.61  thf('30', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.42/0.61  thf('31', plain,
% 0.42/0.61      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.42/0.61      inference('split', [status(esa)], ['3'])).
% 0.42/0.61  thf('32', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.42/0.61      inference('sup+', [status(thm)], ['30', '31'])).
% 0.42/0.61  thf('33', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('34', plain,
% 0.42/0.61      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.42/0.61         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.42/0.61      inference('sup+', [status(thm)], ['32', '33'])).
% 0.42/0.61  thf('35', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['22', '25'])).
% 0.42/0.61  thf('36', plain,
% 0.42/0.61      (((r2_hidden @ sk_A @ 
% 0.42/0.61         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))))
% 0.42/0.61         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.42/0.61      inference('sup+', [status(thm)], ['34', '35'])).
% 0.42/0.61  thf(l1_zfmisc_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.42/0.61  thf('37', plain,
% 0.42/0.61      (![X35 : $i, X37 : $i]:
% 0.42/0.61         ((r1_tarski @ (k1_tarski @ X35) @ X37) | ~ (r2_hidden @ X35 @ X37))),
% 0.42/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.42/0.61  thf('38', plain,
% 0.42/0.61      (((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.42/0.61         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))))
% 0.42/0.61         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['36', '37'])).
% 0.42/0.61  thf(t135_zfmisc_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.42/0.61         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.42/0.61       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.61  thf('39', plain,
% 0.42/0.61      (![X45 : $i, X46 : $i]:
% 0.42/0.61         (((X45) = (k1_xboole_0))
% 0.42/0.61          | ~ (r1_tarski @ X45 @ (k2_zfmisc_1 @ X45 @ X46)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.42/0.61  thf('40', plain,
% 0.42/0.61      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.42/0.61         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.42/0.61  thf(t20_zfmisc_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.42/0.61         ( k1_tarski @ A ) ) <=>
% 0.42/0.61       ( ( A ) != ( B ) ) ))).
% 0.42/0.61  thf('41', plain,
% 0.42/0.61      (![X47 : $i, X48 : $i]:
% 0.42/0.61         (((X48) != (X47))
% 0.42/0.61          | ((k4_xboole_0 @ (k1_tarski @ X48) @ (k1_tarski @ X47))
% 0.42/0.61              != (k1_tarski @ X48)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.42/0.61  thf('42', plain,
% 0.42/0.61      (![X47 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ (k1_tarski @ X47) @ (k1_tarski @ X47))
% 0.42/0.61           != (k1_tarski @ X47))),
% 0.42/0.61      inference('simplify', [status(thm)], ['41'])).
% 0.42/0.61  thf(idempotence_k3_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.42/0.61  thf('43', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.42/0.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.42/0.61  thf(t100_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.42/0.61  thf('44', plain,
% 0.42/0.61      (![X1 : $i, X2 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X1 @ X2)
% 0.42/0.61           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.61  thf('45', plain,
% 0.42/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['43', '44'])).
% 0.42/0.61  thf(t21_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.42/0.61  thf('46', plain,
% 0.42/0.61      (![X3 : $i, X4 : $i]:
% 0.42/0.61         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (X3))),
% 0.42/0.61      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.42/0.61  thf('47', plain,
% 0.42/0.61      (![X1 : $i, X2 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X1 @ X2)
% 0.42/0.61           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.61  thf('48', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.42/0.61           = (k5_xboole_0 @ X0 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['46', '47'])).
% 0.42/0.61  thf(t46_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.42/0.61  thf('49', plain,
% 0.42/0.61      (![X5 : $i, X6 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.42/0.61      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.42/0.61  thf('50', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['48', '49'])).
% 0.42/0.61  thf('51', plain, (![X47 : $i]: ((k1_xboole_0) != (k1_tarski @ X47))),
% 0.42/0.61      inference('demod', [status(thm)], ['42', '45', '50'])).
% 0.42/0.61  thf('52', plain,
% 0.42/0.61      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['40', '51'])).
% 0.42/0.61  thf('53', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['52'])).
% 0.42/0.61  thf('54', plain,
% 0.42/0.61      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.42/0.61      inference('split', [status(esa)], ['3'])).
% 0.42/0.61  thf('55', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.42/0.61      inference('sat_resolution*', [status(thm)], ['53', '54'])).
% 0.42/0.61  thf('56', plain,
% 0.42/0.61      ((r2_hidden @ sk_A @ 
% 0.42/0.61        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.42/0.61      inference('simpl_trail', [status(thm)], ['27', '55'])).
% 0.42/0.61  thf('57', plain,
% 0.42/0.61      (![X35 : $i, X37 : $i]:
% 0.42/0.61         ((r1_tarski @ (k1_tarski @ X35) @ X37) | ~ (r2_hidden @ X35 @ X37))),
% 0.42/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.42/0.61  thf('58', plain,
% 0.42/0.61      ((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.42/0.61        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['56', '57'])).
% 0.42/0.61  thf('59', plain,
% 0.42/0.61      (![X45 : $i, X46 : $i]:
% 0.42/0.61         (((X45) = (k1_xboole_0))
% 0.42/0.61          | ~ (r1_tarski @ X45 @ (k2_zfmisc_1 @ X46 @ X45)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.42/0.61  thf('60', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['58', '59'])).
% 0.42/0.61  thf('61', plain, (![X47 : $i]: ((k1_xboole_0) != (k1_tarski @ X47))),
% 0.42/0.61      inference('demod', [status(thm)], ['42', '45', '50'])).
% 0.42/0.61  thf('62', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['60', '61'])).
% 0.42/0.61  thf('63', plain, ($false), inference('simplify', [status(thm)], ['62'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.45/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
