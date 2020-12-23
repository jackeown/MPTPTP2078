%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eGQlG409Jc

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:07 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 194 expanded)
%              Number of leaves         :   38 (  73 expanded)
%              Depth                    :   20
%              Number of atoms          :  694 (1756 expanded)
%              Number of equality atoms :   87 ( 202 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X65: $i,X67: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X65 @ X67 ) )
      = X67 ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('13',plain,(
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

thf('14',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( zip_tseitin_0 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 )
      | ( r2_hidden @ X53 @ X60 )
      | ( X60
       != ( k4_enumset1 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( r2_hidden @ X53 @ ( k4_enumset1 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 ) )
      | ( zip_tseitin_0 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X46 != X45 )
      | ~ ( zip_tseitin_0 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    ! [X45: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ~ ( zip_tseitin_0 @ X45 @ X47 @ X48 @ X49 @ X50 @ X51 @ X45 ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X39: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X35 @ X37 ) @ ( k2_zfmisc_1 @ X36 @ X39 ) )
      | ~ ( r2_hidden @ X37 @ X39 )
      | ~ ( r2_hidden @ X35 @ X36 ) ) ),
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
    ! [X65: $i,X66: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X65 @ X66 ) )
      = X65 ) ),
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
    ! [X32: $i,X34: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X32 ) @ X34 )
      | ~ ( r2_hidden @ X32 @ X34 ) ) ),
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
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( r1_tarski @ X40 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ),
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
    ! [X42: $i,X43: $i] :
      ( ( X43 != X42 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X42 ) )
       != ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('42',plain,(
    ! [X42: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X42 ) @ ( k1_tarski @ X42 ) )
     != ( k1_tarski @ X42 ) ) ),
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

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('46',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('47',plain,(
    ! [X42: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X42 ) ) ),
    inference(demod,[status(thm)],['42','45','46'])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('51',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['27','51'])).

thf('53',plain,(
    ! [X32: $i,X34: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X32 ) @ X34 )
      | ~ ( r2_hidden @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('54',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( r1_tarski @ X40 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('56',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X42: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X42 ) ) ),
    inference(demod,[status(thm)],['42','45','46'])).

thf('58',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(simplify,[status(thm)],['58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eGQlG409Jc
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:44:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.38/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.63  % Solved by: fo/fo7.sh
% 0.38/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.63  % done 441 iterations in 0.165s
% 0.38/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.63  % SZS output start Refutation
% 0.38/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.38/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.63  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.38/0.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.63  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.38/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.63  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.38/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.38/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.63  thf(t20_mcart_1, conjecture,
% 0.38/0.63    (![A:$i]:
% 0.38/0.63     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.38/0.63       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.38/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.63    (~( ![A:$i]:
% 0.38/0.63        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.38/0.63          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.38/0.63    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.38/0.63  thf('0', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf(t7_mcart_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.38/0.63       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.38/0.63  thf('1', plain,
% 0.38/0.63      (![X65 : $i, X67 : $i]: ((k2_mcart_1 @ (k4_tarski @ X65 @ X67)) = (X67))),
% 0.38/0.63      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.38/0.63  thf('2', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.38/0.63      inference('sup+', [status(thm)], ['0', '1'])).
% 0.38/0.63  thf('3', plain,
% 0.38/0.63      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('4', plain,
% 0.38/0.63      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.63      inference('split', [status(esa)], ['3'])).
% 0.38/0.63  thf('5', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.63      inference('sup+', [status(thm)], ['2', '4'])).
% 0.38/0.63  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('7', plain,
% 0.38/0.63      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.38/0.63         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.63      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.63  thf(t70_enumset1, axiom,
% 0.38/0.63    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.38/0.63  thf('8', plain,
% 0.38/0.63      (![X5 : $i, X6 : $i]:
% 0.38/0.63         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.38/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.63  thf(t69_enumset1, axiom,
% 0.38/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.63  thf('9', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.38/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.63  thf('10', plain,
% 0.38/0.63      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['8', '9'])).
% 0.38/0.63  thf(t71_enumset1, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.38/0.63  thf('11', plain,
% 0.38/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.63         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.38/0.63      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.38/0.63  thf(t72_enumset1, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.63     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.38/0.63  thf('12', plain,
% 0.38/0.63      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.63         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.38/0.63           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.38/0.63      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.38/0.63  thf(t73_enumset1, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.38/0.63     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.38/0.63       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.38/0.63  thf('13', plain,
% 0.38/0.63      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.63         ((k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.38/0.63           = (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.38/0.63      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.38/0.63  thf(d4_enumset1, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.38/0.63     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.38/0.63       ( ![H:$i]:
% 0.38/0.63         ( ( r2_hidden @ H @ G ) <=>
% 0.38/0.63           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.38/0.63                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.38/0.63  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.38/0.63  thf(zf_stmt_2, axiom,
% 0.38/0.63    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.38/0.63     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.38/0.63       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.38/0.63         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.38/0.63  thf(zf_stmt_3, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.38/0.63     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.38/0.63       ( ![H:$i]:
% 0.38/0.63         ( ( r2_hidden @ H @ G ) <=>
% 0.38/0.63           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.38/0.63  thf('14', plain,
% 0.38/0.63      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, 
% 0.38/0.63         X60 : $i]:
% 0.38/0.63         ((zip_tseitin_0 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59)
% 0.38/0.63          | (r2_hidden @ X53 @ X60)
% 0.38/0.63          | ((X60) != (k4_enumset1 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54)))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.63  thf('15', plain,
% 0.38/0.63      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.38/0.63         ((r2_hidden @ X53 @ (k4_enumset1 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54))
% 0.38/0.63          | (zip_tseitin_0 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59))),
% 0.38/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.38/0.63  thf('16', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.63         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.38/0.63          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.38/0.63      inference('sup+', [status(thm)], ['13', '15'])).
% 0.38/0.63  thf('17', plain,
% 0.38/0.63      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.38/0.63         (((X46) != (X45))
% 0.38/0.63          | ~ (zip_tseitin_0 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X45))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.63  thf('18', plain,
% 0.38/0.63      (![X45 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.38/0.63         ~ (zip_tseitin_0 @ X45 @ X47 @ X48 @ X49 @ X50 @ X51 @ X45)),
% 0.38/0.63      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.63  thf('19', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.63         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.38/0.63      inference('sup-', [status(thm)], ['16', '18'])).
% 0.38/0.63  thf('20', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.63         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['12', '19'])).
% 0.38/0.63  thf('21', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.63         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['11', '20'])).
% 0.38/0.63  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['10', '21'])).
% 0.38/0.63  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['10', '21'])).
% 0.38/0.63  thf(l54_zfmisc_1, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.63     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.38/0.63       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.38/0.63  thf('24', plain,
% 0.38/0.63      (![X35 : $i, X36 : $i, X37 : $i, X39 : $i]:
% 0.38/0.63         ((r2_hidden @ (k4_tarski @ X35 @ X37) @ (k2_zfmisc_1 @ X36 @ X39))
% 0.38/0.63          | ~ (r2_hidden @ X37 @ X39)
% 0.38/0.63          | ~ (r2_hidden @ X35 @ X36))),
% 0.38/0.63      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.38/0.63  thf('25', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X2 @ X1)
% 0.38/0.63          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.38/0.63             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.63  thf('26', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.38/0.63          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['22', '25'])).
% 0.38/0.63  thf('27', plain,
% 0.38/0.63      (((r2_hidden @ sk_A @ 
% 0.38/0.63         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))
% 0.38/0.63         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.63      inference('sup+', [status(thm)], ['7', '26'])).
% 0.38/0.63  thf('28', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('29', plain,
% 0.38/0.63      (![X65 : $i, X66 : $i]: ((k1_mcart_1 @ (k4_tarski @ X65 @ X66)) = (X65))),
% 0.38/0.63      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.38/0.63  thf('30', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.38/0.63      inference('sup+', [status(thm)], ['28', '29'])).
% 0.38/0.63  thf('31', plain,
% 0.38/0.63      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.63      inference('split', [status(esa)], ['3'])).
% 0.38/0.63  thf('32', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.63      inference('sup+', [status(thm)], ['30', '31'])).
% 0.38/0.63  thf('33', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('34', plain,
% 0.38/0.63      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.38/0.63         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.63      inference('sup+', [status(thm)], ['32', '33'])).
% 0.38/0.63  thf('35', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.38/0.63          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['22', '25'])).
% 0.38/0.63  thf('36', plain,
% 0.38/0.63      (((r2_hidden @ sk_A @ 
% 0.38/0.63         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))))
% 0.38/0.63         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.63      inference('sup+', [status(thm)], ['34', '35'])).
% 0.38/0.63  thf(l1_zfmisc_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.38/0.63  thf('37', plain,
% 0.38/0.63      (![X32 : $i, X34 : $i]:
% 0.38/0.63         ((r1_tarski @ (k1_tarski @ X32) @ X34) | ~ (r2_hidden @ X32 @ X34))),
% 0.38/0.63      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.38/0.63  thf('38', plain,
% 0.38/0.63      (((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.38/0.63         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))))
% 0.38/0.63         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.63  thf(t135_zfmisc_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.38/0.63         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.38/0.63       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.63  thf('39', plain,
% 0.38/0.63      (![X40 : $i, X41 : $i]:
% 0.38/0.63         (((X40) = (k1_xboole_0))
% 0.38/0.63          | ~ (r1_tarski @ X40 @ (k2_zfmisc_1 @ X40 @ X41)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.38/0.63  thf('40', plain,
% 0.38/0.63      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.38/0.63         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.63  thf(t20_zfmisc_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.63         ( k1_tarski @ A ) ) <=>
% 0.38/0.63       ( ( A ) != ( B ) ) ))).
% 0.38/0.63  thf('41', plain,
% 0.38/0.63      (![X42 : $i, X43 : $i]:
% 0.38/0.63         (((X43) != (X42))
% 0.38/0.63          | ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X42))
% 0.38/0.63              != (k1_tarski @ X43)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.38/0.63  thf('42', plain,
% 0.38/0.63      (![X42 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ (k1_tarski @ X42) @ (k1_tarski @ X42))
% 0.38/0.63           != (k1_tarski @ X42))),
% 0.38/0.63      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.63  thf(idempotence_k3_xboole_0, axiom,
% 0.38/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.38/0.63  thf('43', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.63      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.38/0.63  thf(t100_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.63  thf('44', plain,
% 0.38/0.63      (![X1 : $i, X2 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X1 @ X2)
% 0.38/0.63           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.63  thf('45', plain,
% 0.38/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['43', '44'])).
% 0.38/0.63  thf(t92_xboole_1, axiom,
% 0.38/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.63  thf('46', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.38/0.63      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.63  thf('47', plain, (![X42 : $i]: ((k1_xboole_0) != (k1_tarski @ X42))),
% 0.38/0.63      inference('demod', [status(thm)], ['42', '45', '46'])).
% 0.38/0.63  thf('48', plain,
% 0.38/0.63      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['40', '47'])).
% 0.38/0.63  thf('49', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.38/0.63      inference('simplify', [status(thm)], ['48'])).
% 0.38/0.63  thf('50', plain,
% 0.38/0.63      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.38/0.63      inference('split', [status(esa)], ['3'])).
% 0.38/0.63  thf('51', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.38/0.63      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.38/0.63  thf('52', plain,
% 0.38/0.63      ((r2_hidden @ sk_A @ 
% 0.38/0.63        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.38/0.63      inference('simpl_trail', [status(thm)], ['27', '51'])).
% 0.38/0.63  thf('53', plain,
% 0.38/0.63      (![X32 : $i, X34 : $i]:
% 0.38/0.63         ((r1_tarski @ (k1_tarski @ X32) @ X34) | ~ (r2_hidden @ X32 @ X34))),
% 0.38/0.63      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.38/0.63  thf('54', plain,
% 0.38/0.63      ((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.38/0.63        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.63  thf('55', plain,
% 0.38/0.63      (![X40 : $i, X41 : $i]:
% 0.38/0.63         (((X40) = (k1_xboole_0))
% 0.38/0.63          | ~ (r1_tarski @ X40 @ (k2_zfmisc_1 @ X41 @ X40)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.38/0.63  thf('56', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.63  thf('57', plain, (![X42 : $i]: ((k1_xboole_0) != (k1_tarski @ X42))),
% 0.38/0.63      inference('demod', [status(thm)], ['42', '45', '46'])).
% 0.38/0.63  thf('58', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.63  thf('59', plain, ($false), inference('simplify', [status(thm)], ['58'])).
% 0.38/0.63  
% 0.38/0.63  % SZS output end Refutation
% 0.38/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
