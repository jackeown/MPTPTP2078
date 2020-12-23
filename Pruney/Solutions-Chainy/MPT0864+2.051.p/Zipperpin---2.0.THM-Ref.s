%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vwcKI02lQI

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:06 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 186 expanded)
%              Number of leaves         :   35 (  69 expanded)
%              Depth                    :   19
%              Number of atoms          :  665 (1614 expanded)
%              Number of equality atoms :   78 ( 181 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i,X65: $i,X66: $i,X67: $i] :
      ( ( zip_tseitin_0 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 )
      | ( r2_hidden @ X61 @ X67 )
      | ( X67
       != ( k3_enumset1 @ X66 @ X65 @ X64 @ X63 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ( r2_hidden @ X61 @ ( k3_enumset1 @ X66 @ X65 @ X64 @ X63 @ X62 ) )
      | ( zip_tseitin_0 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( X55 != X54 )
      | ~ ( zip_tseitin_0 @ X55 @ X56 @ X57 @ X58 @ X59 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    ! [X54: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ~ ( zip_tseitin_0 @ X54 @ X56 @ X57 @ X58 @ X59 @ X54 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('22',plain,(
    ! [X39: $i,X40: $i,X41: $i,X43: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X39 @ X41 ) @ ( k2_zfmisc_1 @ X40 @ X43 ) )
      | ~ ( r2_hidden @ X41 @ X43 )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','24'])).

thf('26',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X70: $i,X71: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X70 @ X71 ) )
      = X70 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('28',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('35',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('36',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( r1_tarski @ X44 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('38',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X50 @ X51 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X50 @ X52 ) @ X51 )
       != ( k2_tarski @ X50 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( r2_hidden @ X46 @ X47 )
      | ~ ( r1_tarski @ ( k2_tarski @ X46 @ X48 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','47'])).

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
    inference(simpl_trail,[status(thm)],['25','51'])).

thf('53',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('54',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( r1_tarski @ X44 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('56',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('58',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(simplify,[status(thm)],['58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vwcKI02lQI
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:49:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.58/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.86  % Solved by: fo/fo7.sh
% 0.58/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.86  % done 802 iterations in 0.398s
% 0.58/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.86  % SZS output start Refutation
% 0.58/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.86  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.58/0.86  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.58/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.86  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.58/0.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.86  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.58/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.86  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.58/0.86  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 0.58/0.86  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.58/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.86  thf(t20_mcart_1, conjecture,
% 0.58/0.86    (![A:$i]:
% 0.58/0.86     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.58/0.86       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.58/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.86    (~( ![A:$i]:
% 0.58/0.86        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.58/0.86          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.58/0.86    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.58/0.86  thf('0', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.58/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.86  thf(t7_mcart_1, axiom,
% 0.58/0.86    (![A:$i,B:$i]:
% 0.58/0.86     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.58/0.86       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.58/0.86  thf('1', plain,
% 0.58/0.86      (![X70 : $i, X72 : $i]: ((k2_mcart_1 @ (k4_tarski @ X70 @ X72)) = (X72))),
% 0.58/0.86      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.58/0.86  thf('2', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.58/0.86      inference('sup+', [status(thm)], ['0', '1'])).
% 0.58/0.86  thf('3', plain,
% 0.58/0.86      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.58/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.86  thf('4', plain,
% 0.58/0.86      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.58/0.86      inference('split', [status(esa)], ['3'])).
% 0.58/0.86  thf('5', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.58/0.86      inference('sup+', [status(thm)], ['2', '4'])).
% 0.58/0.86  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.58/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.86  thf('7', plain,
% 0.58/0.86      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.58/0.86         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.58/0.86      inference('sup+', [status(thm)], ['5', '6'])).
% 0.58/0.86  thf(t70_enumset1, axiom,
% 0.58/0.86    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.58/0.86  thf('8', plain,
% 0.58/0.86      (![X7 : $i, X8 : $i]:
% 0.58/0.86         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.58/0.86      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.86  thf(t69_enumset1, axiom,
% 0.58/0.86    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.58/0.86  thf('9', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.58/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.86  thf('10', plain,
% 0.58/0.86      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.58/0.86      inference('sup+', [status(thm)], ['8', '9'])).
% 0.58/0.86  thf(t71_enumset1, axiom,
% 0.58/0.86    (![A:$i,B:$i,C:$i]:
% 0.58/0.86     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.58/0.86  thf('11', plain,
% 0.58/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.86         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.58/0.86      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.58/0.86  thf(t72_enumset1, axiom,
% 0.58/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.86     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.58/0.86  thf('12', plain,
% 0.58/0.86      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.86         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 0.58/0.86           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 0.58/0.86      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.58/0.86  thf(d3_enumset1, axiom,
% 0.58/0.86    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.58/0.86     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.58/0.86       ( ![G:$i]:
% 0.58/0.86         ( ( r2_hidden @ G @ F ) <=>
% 0.58/0.86           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 0.58/0.86                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 0.58/0.86  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 0.58/0.86  thf(zf_stmt_2, axiom,
% 0.58/0.86    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.58/0.86     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 0.58/0.86       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 0.58/0.86         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 0.58/0.86  thf(zf_stmt_3, axiom,
% 0.58/0.86    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.58/0.86     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.58/0.86       ( ![G:$i]:
% 0.58/0.86         ( ( r2_hidden @ G @ F ) <=>
% 0.58/0.86           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.58/0.86  thf('13', plain,
% 0.58/0.86      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i, X67 : $i]:
% 0.58/0.86         ((zip_tseitin_0 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66)
% 0.58/0.86          | (r2_hidden @ X61 @ X67)
% 0.58/0.86          | ((X67) != (k3_enumset1 @ X66 @ X65 @ X64 @ X63 @ X62)))),
% 0.58/0.86      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.86  thf('14', plain,
% 0.58/0.86      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 0.58/0.86         ((r2_hidden @ X61 @ (k3_enumset1 @ X66 @ X65 @ X64 @ X63 @ X62))
% 0.58/0.86          | (zip_tseitin_0 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66))),
% 0.58/0.86      inference('simplify', [status(thm)], ['13'])).
% 0.58/0.86  thf('15', plain,
% 0.58/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.86         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.58/0.86          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.58/0.86      inference('sup+', [status(thm)], ['12', '14'])).
% 0.58/0.86  thf('16', plain,
% 0.58/0.86      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.58/0.86         (((X55) != (X54))
% 0.58/0.86          | ~ (zip_tseitin_0 @ X55 @ X56 @ X57 @ X58 @ X59 @ X54))),
% 0.58/0.86      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.86  thf('17', plain,
% 0.58/0.86      (![X54 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.58/0.86         ~ (zip_tseitin_0 @ X54 @ X56 @ X57 @ X58 @ X59 @ X54)),
% 0.58/0.86      inference('simplify', [status(thm)], ['16'])).
% 0.58/0.86  thf('18', plain,
% 0.58/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.86         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.58/0.86      inference('sup-', [status(thm)], ['15', '17'])).
% 0.58/0.86  thf('19', plain,
% 0.58/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.86         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.58/0.86      inference('sup+', [status(thm)], ['11', '18'])).
% 0.58/0.86  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.58/0.86      inference('sup+', [status(thm)], ['10', '19'])).
% 0.58/0.86  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.58/0.86      inference('sup+', [status(thm)], ['10', '19'])).
% 0.58/0.86  thf(l54_zfmisc_1, axiom,
% 0.58/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.86     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.58/0.86       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.58/0.86  thf('22', plain,
% 0.58/0.86      (![X39 : $i, X40 : $i, X41 : $i, X43 : $i]:
% 0.58/0.86         ((r2_hidden @ (k4_tarski @ X39 @ X41) @ (k2_zfmisc_1 @ X40 @ X43))
% 0.58/0.86          | ~ (r2_hidden @ X41 @ X43)
% 0.58/0.86          | ~ (r2_hidden @ X39 @ X40))),
% 0.58/0.86      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.58/0.86  thf('23', plain,
% 0.58/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.86         (~ (r2_hidden @ X2 @ X1)
% 0.58/0.86          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.58/0.86             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.58/0.86      inference('sup-', [status(thm)], ['21', '22'])).
% 0.58/0.86  thf('24', plain,
% 0.58/0.86      (![X0 : $i, X1 : $i]:
% 0.58/0.86         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.58/0.86          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.58/0.86      inference('sup-', [status(thm)], ['20', '23'])).
% 0.58/0.86  thf('25', plain,
% 0.58/0.86      (((r2_hidden @ sk_A @ 
% 0.58/0.86         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))
% 0.58/0.86         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.58/0.86      inference('sup+', [status(thm)], ['7', '24'])).
% 0.58/0.86  thf('26', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.58/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.86  thf('27', plain,
% 0.58/0.86      (![X70 : $i, X71 : $i]: ((k1_mcart_1 @ (k4_tarski @ X70 @ X71)) = (X70))),
% 0.58/0.86      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.58/0.86  thf('28', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.58/0.86      inference('sup+', [status(thm)], ['26', '27'])).
% 0.58/0.86  thf('29', plain,
% 0.58/0.86      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.58/0.86      inference('split', [status(esa)], ['3'])).
% 0.58/0.86  thf('30', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.58/0.86      inference('sup+', [status(thm)], ['28', '29'])).
% 0.58/0.86  thf('31', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.58/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.86  thf('32', plain,
% 0.58/0.86      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.58/0.86         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.58/0.86      inference('sup+', [status(thm)], ['30', '31'])).
% 0.58/0.86  thf('33', plain,
% 0.58/0.86      (![X0 : $i, X1 : $i]:
% 0.58/0.86         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.58/0.86          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.58/0.86      inference('sup-', [status(thm)], ['20', '23'])).
% 0.58/0.86  thf('34', plain,
% 0.58/0.86      (((r2_hidden @ sk_A @ 
% 0.58/0.86         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))))
% 0.58/0.86         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.58/0.86      inference('sup+', [status(thm)], ['32', '33'])).
% 0.58/0.86  thf(l1_zfmisc_1, axiom,
% 0.58/0.86    (![A:$i,B:$i]:
% 0.58/0.86     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.58/0.86  thf('35', plain,
% 0.58/0.86      (![X34 : $i, X36 : $i]:
% 0.58/0.86         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 0.58/0.86      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.58/0.86  thf('36', plain,
% 0.58/0.86      (((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.58/0.86         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))))
% 0.58/0.86         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.58/0.86      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.86  thf(t135_zfmisc_1, axiom,
% 0.58/0.86    (![A:$i,B:$i]:
% 0.58/0.86     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.58/0.86         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.58/0.86       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.58/0.86  thf('37', plain,
% 0.58/0.86      (![X44 : $i, X45 : $i]:
% 0.58/0.86         (((X44) = (k1_xboole_0))
% 0.58/0.86          | ~ (r1_tarski @ X44 @ (k2_zfmisc_1 @ X44 @ X45)))),
% 0.58/0.86      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.58/0.86  thf('38', plain,
% 0.58/0.86      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.58/0.86         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.58/0.86      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.86  thf('39', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.58/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.86  thf(t46_xboole_1, axiom,
% 0.58/0.86    (![A:$i,B:$i]:
% 0.58/0.86     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.58/0.86  thf('40', plain,
% 0.58/0.86      (![X0 : $i, X1 : $i]:
% 0.58/0.86         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.58/0.86      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.58/0.86  thf(t72_zfmisc_1, axiom,
% 0.58/0.86    (![A:$i,B:$i,C:$i]:
% 0.58/0.86     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.58/0.86       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.58/0.86  thf('41', plain,
% 0.58/0.86      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.58/0.86         (~ (r2_hidden @ X50 @ X51)
% 0.58/0.86          | ((k4_xboole_0 @ (k2_tarski @ X50 @ X52) @ X51)
% 0.58/0.86              != (k2_tarski @ X50 @ X52)))),
% 0.58/0.86      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.58/0.86  thf('42', plain,
% 0.58/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.86         (((k1_xboole_0) != (k2_tarski @ X1 @ X0))
% 0.58/0.86          | ~ (r2_hidden @ X1 @ (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.58/0.86      inference('sup-', [status(thm)], ['40', '41'])).
% 0.58/0.86  thf(t7_xboole_1, axiom,
% 0.58/0.86    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.86  thf('43', plain,
% 0.58/0.86      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 0.58/0.86      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.58/0.86  thf(t38_zfmisc_1, axiom,
% 0.58/0.86    (![A:$i,B:$i,C:$i]:
% 0.58/0.86     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.58/0.86       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.58/0.86  thf('44', plain,
% 0.58/0.86      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.58/0.86         ((r2_hidden @ X46 @ X47)
% 0.58/0.86          | ~ (r1_tarski @ (k2_tarski @ X46 @ X48) @ X47))),
% 0.58/0.86      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.58/0.86  thf('45', plain,
% 0.58/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.86         (r2_hidden @ X2 @ (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0))),
% 0.58/0.86      inference('sup-', [status(thm)], ['43', '44'])).
% 0.58/0.86  thf('46', plain,
% 0.58/0.86      (![X0 : $i, X1 : $i]: ((k1_xboole_0) != (k2_tarski @ X1 @ X0))),
% 0.58/0.86      inference('demod', [status(thm)], ['42', '45'])).
% 0.58/0.86  thf('47', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.58/0.86      inference('sup-', [status(thm)], ['39', '46'])).
% 0.58/0.86  thf('48', plain,
% 0.58/0.86      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.58/0.86      inference('sup-', [status(thm)], ['38', '47'])).
% 0.58/0.86  thf('49', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.58/0.86      inference('simplify', [status(thm)], ['48'])).
% 0.58/0.86  thf('50', plain,
% 0.58/0.86      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.58/0.86      inference('split', [status(esa)], ['3'])).
% 0.58/0.86  thf('51', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.58/0.86      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.58/0.86  thf('52', plain,
% 0.58/0.86      ((r2_hidden @ sk_A @ 
% 0.58/0.86        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.58/0.86      inference('simpl_trail', [status(thm)], ['25', '51'])).
% 0.58/0.86  thf('53', plain,
% 0.58/0.86      (![X34 : $i, X36 : $i]:
% 0.58/0.86         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 0.58/0.86      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.58/0.86  thf('54', plain,
% 0.58/0.86      ((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.58/0.86        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.58/0.86      inference('sup-', [status(thm)], ['52', '53'])).
% 0.58/0.86  thf('55', plain,
% 0.58/0.86      (![X44 : $i, X45 : $i]:
% 0.58/0.86         (((X44) = (k1_xboole_0))
% 0.58/0.86          | ~ (r1_tarski @ X44 @ (k2_zfmisc_1 @ X45 @ X44)))),
% 0.58/0.86      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.58/0.86  thf('56', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.58/0.86      inference('sup-', [status(thm)], ['54', '55'])).
% 0.58/0.86  thf('57', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.58/0.86      inference('sup-', [status(thm)], ['39', '46'])).
% 0.58/0.86  thf('58', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.58/0.86      inference('sup-', [status(thm)], ['56', '57'])).
% 0.58/0.86  thf('59', plain, ($false), inference('simplify', [status(thm)], ['58'])).
% 0.58/0.86  
% 0.58/0.86  % SZS output end Refutation
% 0.58/0.86  
% 0.69/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
