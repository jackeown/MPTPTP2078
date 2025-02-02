%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iDdtKJo9PU

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:07 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 146 expanded)
%              Number of leaves         :   38 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  656 (1202 expanded)
%              Number of equality atoms :   86 ( 162 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
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
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( zip_tseitin_0 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 )
      | ( r2_hidden @ X50 @ X57 )
      | ( X57
       != ( k4_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( r2_hidden @ X50 @ ( k4_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 ) )
      | ( zip_tseitin_0 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( X43 != X42 )
      | ~ ( zip_tseitin_0 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X42: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ~ ( zip_tseitin_0 @ X42 @ X44 @ X45 @ X46 @ X47 @ X48 @ X42 ) ),
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
    ! [X32: $i,X34: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X32 ) @ X34 )
      | ~ ( r2_hidden @ X32 @ X34 ) ) ),
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
    ! [X62: $i,X64: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X62 @ X64 ) )
      = X64 ) ),
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
    ! [X40: $i,X41: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X40 ) @ ( k1_tarski @ X41 ) )
      = ( k1_tarski @ ( k4_tarski @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ( X38 != X37 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X37 ) )
       != ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('29',plain,(
    ! [X37: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X37 ) )
     != ( k1_tarski @ X37 ) ) ),
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

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('33',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('34',plain,(
    ! [X37: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X37 ) ) ),
    inference(demod,[status(thm)],['29','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['27','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('39',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X62: $i,X63: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X62 @ X63 ) )
      = X62 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('41',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('43',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X40 ) @ ( k1_tarski @ X41 ) )
      = ( k1_tarski @ ( k4_tarski @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('47',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X37: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X37 ) ) ),
    inference(demod,[status(thm)],['29','32','33'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','51'])).

thf('53',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('54',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['37','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iDdtKJo9PU
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 324 iterations in 0.126s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.39/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.39/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.39/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.39/0.58  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.39/0.58  thf(t70_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i]:
% 0.39/0.58         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.39/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.58  thf(t69_enumset1, axiom,
% 0.39/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.58  thf('1', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.39/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['0', '1'])).
% 0.39/0.58  thf(t71_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.58         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.39/0.58  thf(t72_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.58     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.58         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.39/0.58           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.39/0.58      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.39/0.58  thf(t73_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.39/0.58     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.39/0.58       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.58         ((k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.39/0.58           = (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.39/0.58      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.39/0.58  thf(d4_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.39/0.58     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.39/0.58       ( ![H:$i]:
% 0.39/0.58         ( ( r2_hidden @ H @ G ) <=>
% 0.39/0.58           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.39/0.58                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_1, axiom,
% 0.39/0.58    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.39/0.58     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.39/0.58       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.39/0.58         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_2, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.39/0.58     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.39/0.58       ( ![H:$i]:
% 0.39/0.58         ( ( r2_hidden @ H @ G ) <=>
% 0.39/0.58           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, 
% 0.39/0.58         X57 : $i]:
% 0.39/0.58         ((zip_tseitin_0 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56)
% 0.39/0.58          | (r2_hidden @ X50 @ X57)
% 0.39/0.58          | ((X57) != (k4_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.39/0.58         ((r2_hidden @ X50 @ (k4_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51))
% 0.39/0.58          | (zip_tseitin_0 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56))),
% 0.39/0.58      inference('simplify', [status(thm)], ['6'])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.58         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.58          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.39/0.58      inference('sup+', [status(thm)], ['5', '7'])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.39/0.58         (((X43) != (X42))
% 0.39/0.58          | ~ (zip_tseitin_0 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X42))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X42 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.39/0.58         ~ (zip_tseitin_0 @ X42 @ X44 @ X45 @ X46 @ X47 @ X48 @ X42)),
% 0.39/0.58      inference('simplify', [status(thm)], ['9'])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.58         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.39/0.58      inference('sup-', [status(thm)], ['8', '10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['4', '11'])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['3', '12'])).
% 0.39/0.58  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['2', '13'])).
% 0.39/0.58  thf(l1_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X32 : $i, X34 : $i]:
% 0.39/0.58         ((r1_tarski @ (k1_tarski @ X32) @ X34) | ~ (r2_hidden @ X32 @ X34))),
% 0.39/0.58      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.58  thf(t20_mcart_1, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.39/0.58       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_3, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.39/0.58          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.39/0.58  thf('17', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.58  thf(t7_mcart_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.39/0.58       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X62 : $i, X64 : $i]: ((k2_mcart_1 @ (k4_tarski @ X62 @ X64)) = (X64))),
% 0.39/0.58      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.39/0.58  thf('19', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.39/0.58      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.39/0.58      inference('split', [status(esa)], ['20'])).
% 0.39/0.58  thf('22', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['19', '21'])).
% 0.39/0.58  thf('23', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.39/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['22', '23'])).
% 0.39/0.58  thf(t35_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.39/0.58       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X40 : $i, X41 : $i]:
% 0.39/0.58         ((k2_zfmisc_1 @ (k1_tarski @ X40) @ (k1_tarski @ X41))
% 0.39/0.58           = (k1_tarski @ (k4_tarski @ X40 @ X41)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.39/0.58  thf(t135_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.39/0.58         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.39/0.58       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (![X35 : $i, X36 : $i]:
% 0.39/0.58         (((X35) = (k1_xboole_0))
% 0.39/0.58          | ~ (r1_tarski @ X35 @ (k2_zfmisc_1 @ X36 @ X35)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.39/0.58          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.58  thf(t20_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.39/0.58         ( k1_tarski @ A ) ) <=>
% 0.39/0.58       ( ( A ) != ( B ) ) ))).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      (![X37 : $i, X38 : $i]:
% 0.39/0.58         (((X38) != (X37))
% 0.39/0.58          | ((k4_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X37))
% 0.39/0.58              != (k1_tarski @ X38)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X37 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X37))
% 0.39/0.58           != (k1_tarski @ X37))),
% 0.39/0.58      inference('simplify', [status(thm)], ['28'])).
% 0.39/0.58  thf(idempotence_k3_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.39/0.58  thf('30', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.39/0.58      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.39/0.58  thf(t100_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (![X1 : $i, X2 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X1 @ X2)
% 0.39/0.58           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf(t92_xboole_1, axiom,
% 0.39/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.39/0.58  thf('33', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.39/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.39/0.58  thf('34', plain, (![X37 : $i]: ((k1_xboole_0) != (k1_tarski @ X37))),
% 0.39/0.58      inference('demod', [status(thm)], ['29', '32', '33'])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.39/0.58      inference('clc', [status(thm)], ['27', '34'])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.39/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['24', '35'])).
% 0.39/0.58  thf('37', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['16', '36'])).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.58  thf('39', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.58  thf('40', plain,
% 0.39/0.58      (![X62 : $i, X63 : $i]: ((k1_mcart_1 @ (k4_tarski @ X62 @ X63)) = (X62))),
% 0.39/0.58      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.39/0.58  thf('41', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['39', '40'])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.39/0.58      inference('split', [status(esa)], ['20'])).
% 0.39/0.58  thf('43', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['41', '42'])).
% 0.39/0.58  thf('44', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.39/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['43', '44'])).
% 0.39/0.58  thf('46', plain,
% 0.39/0.58      (![X40 : $i, X41 : $i]:
% 0.39/0.58         ((k2_zfmisc_1 @ (k1_tarski @ X40) @ (k1_tarski @ X41))
% 0.39/0.58           = (k1_tarski @ (k4_tarski @ X40 @ X41)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      (![X35 : $i, X36 : $i]:
% 0.39/0.58         (((X35) = (k1_xboole_0))
% 0.39/0.58          | ~ (r1_tarski @ X35 @ (k2_zfmisc_1 @ X35 @ X36)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.39/0.58  thf('48', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.39/0.58          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.58  thf('49', plain, (![X37 : $i]: ((k1_xboole_0) != (k1_tarski @ X37))),
% 0.39/0.58      inference('demod', [status(thm)], ['29', '32', '33'])).
% 0.39/0.58  thf('50', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.39/0.58      inference('clc', [status(thm)], ['48', '49'])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.39/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['45', '50'])).
% 0.39/0.58  thf('52', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['38', '51'])).
% 0.39/0.58  thf('53', plain,
% 0.39/0.58      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['20'])).
% 0.39/0.58  thf('54', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.39/0.58      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.39/0.58  thf('55', plain, ($false),
% 0.39/0.58      inference('simpl_trail', [status(thm)], ['37', '54'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
