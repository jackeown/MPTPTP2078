%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QRUQXRnLaW

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 141 expanded)
%              Number of leaves         :   36 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  640 (1170 expanded)
%              Number of equality atoms :   84 ( 158 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ! [X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( zip_tseitin_0 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 )
      | ( r2_hidden @ X54 @ X61 )
      | ( X61
       != ( k4_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( r2_hidden @ X54 @ ( k4_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55 ) )
      | ( zip_tseitin_0 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( X47 != X46 )
      | ~ ( zip_tseitin_0 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X46: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ~ ( zip_tseitin_0 @ X46 @ X48 @ X49 @ X50 @ X51 @ X52 @ X46 ) ),
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
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
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
    ! [X66: $i,X68: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X66 @ X68 ) )
      = X68 ) ),
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
    ! [X44: $i,X45: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X45 ) )
      = ( k1_tarski @ ( k4_tarski @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X39: $i,X40: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( r1_tarski @ X39 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ( X42 != X41 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X42 ) @ ( k1_tarski @ X41 ) )
       != ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('29',plain,(
    ! [X41: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X41 ) @ ( k1_tarski @ X41 ) )
     != ( k1_tarski @ X41 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X41: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X41 ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['27','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('38',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X66 @ X67 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('40',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('42',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X45 ) )
      = ( k1_tarski @ ( k4_tarski @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('46',plain,(
    ! [X39: $i,X40: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( r1_tarski @ X39 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X41: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X41 ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','50'])).

thf('52',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('53',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['36','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QRUQXRnLaW
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 290 iterations in 0.104s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.21/0.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.56  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.56  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.56  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.56  thf(t70_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i]:
% 0.21/0.56         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.56  thf(t69_enumset1, axiom,
% 0.21/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.56  thf('1', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.21/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.56  thf(t71_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.56         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.56  thf(t72_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 0.21/0.56           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.56  thf(t73_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.56     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.21/0.56       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.56         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.21/0.56           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.21/0.56      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.21/0.56  thf(d4_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.56     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.21/0.56       ( ![H:$i]:
% 0.21/0.56         ( ( r2_hidden @ H @ G ) <=>
% 0.21/0.56           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.21/0.56                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.21/0.56  thf(zf_stmt_1, axiom,
% 0.21/0.56    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.56     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.21/0.56       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.21/0.56         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_2, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.56     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.21/0.56       ( ![H:$i]:
% 0.21/0.56         ( ( r2_hidden @ H @ G ) <=>
% 0.21/0.56           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, 
% 0.21/0.56         X61 : $i]:
% 0.21/0.56         ((zip_tseitin_0 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60)
% 0.21/0.56          | (r2_hidden @ X54 @ X61)
% 0.21/0.56          | ((X61) != (k4_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.21/0.56         ((r2_hidden @ X54 @ (k4_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55))
% 0.21/0.56          | (zip_tseitin_0 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60))),
% 0.21/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.56          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.21/0.56      inference('sup+', [status(thm)], ['5', '7'])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.21/0.56         (((X47) != (X46))
% 0.21/0.56          | ~ (zip_tseitin_0 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X46))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X46 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.21/0.56         ~ (zip_tseitin_0 @ X46 @ X48 @ X49 @ X50 @ X51 @ X52 @ X46)),
% 0.21/0.56      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.56         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['4', '11'])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['3', '12'])).
% 0.21/0.56  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['2', '13'])).
% 0.21/0.56  thf(l1_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X34 : $i, X36 : $i]:
% 0.21/0.56         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 0.21/0.56      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf(t20_mcart_1, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.21/0.56       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_3, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.21/0.56          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.21/0.56  thf('17', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.56  thf(t7_mcart_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.56       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X66 : $i, X68 : $i]: ((k2_mcart_1 @ (k4_tarski @ X66 @ X68)) = (X68))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.56  thf('19', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.21/0.56      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.56      inference('split', [status(esa)], ['20'])).
% 0.21/0.56  thf('22', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['19', '21'])).
% 0.21/0.56  thf('23', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.21/0.56         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf(t35_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.56       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X44 : $i, X45 : $i]:
% 0.21/0.56         ((k2_zfmisc_1 @ (k1_tarski @ X44) @ (k1_tarski @ X45))
% 0.21/0.56           = (k1_tarski @ (k4_tarski @ X44 @ X45)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.21/0.56  thf(t135_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.21/0.56         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.56       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X39 : $i, X40 : $i]:
% 0.21/0.56         (((X39) = (k1_xboole_0))
% 0.21/0.56          | ~ (r1_tarski @ X39 @ (k2_zfmisc_1 @ X40 @ X39)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.21/0.56          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf(t20_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.56         ( k1_tarski @ A ) ) <=>
% 0.21/0.56       ( ( A ) != ( B ) ) ))).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X41 : $i, X42 : $i]:
% 0.21/0.56         (((X42) != (X41))
% 0.21/0.56          | ((k4_xboole_0 @ (k1_tarski @ X42) @ (k1_tarski @ X41))
% 0.21/0.56              != (k1_tarski @ X42)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (![X41 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ (k1_tarski @ X41) @ (k1_tarski @ X41))
% 0.21/0.56           != (k1_tarski @ X41))),
% 0.21/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.56  thf(t1_boole, axiom,
% 0.21/0.56    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.56  thf('30', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.56  thf(t46_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X4 : $i, X5 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.56  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.56  thf('33', plain, (![X41 : $i]: ((k1_xboole_0) != (k1_tarski @ X41))),
% 0.21/0.56      inference('demod', [status(thm)], ['29', '32'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.21/0.56      inference('clc', [status(thm)], ['27', '33'])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.21/0.56         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '34'])).
% 0.21/0.56  thf('36', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['16', '35'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf('38', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X66 : $i, X67 : $i]: ((k1_mcart_1 @ (k4_tarski @ X66 @ X67)) = (X66))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.56  thf('40', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.21/0.56      inference('split', [status(esa)], ['20'])).
% 0.21/0.56  thf('42', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['40', '41'])).
% 0.21/0.56  thf('43', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.21/0.56         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['42', '43'])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      (![X44 : $i, X45 : $i]:
% 0.21/0.56         ((k2_zfmisc_1 @ (k1_tarski @ X44) @ (k1_tarski @ X45))
% 0.21/0.56           = (k1_tarski @ (k4_tarski @ X44 @ X45)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      (![X39 : $i, X40 : $i]:
% 0.21/0.56         (((X39) = (k1_xboole_0))
% 0.21/0.56          | ~ (r1_tarski @ X39 @ (k2_zfmisc_1 @ X39 @ X40)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.21/0.56          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.56  thf('48', plain, (![X41 : $i]: ((k1_xboole_0) != (k1_tarski @ X41))),
% 0.21/0.56      inference('demod', [status(thm)], ['29', '32'])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.21/0.56      inference('clc', [status(thm)], ['47', '48'])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.21/0.56         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['44', '49'])).
% 0.21/0.56  thf('51', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['37', '50'])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.21/0.56      inference('split', [status(esa)], ['20'])).
% 0.21/0.56  thf('53', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.21/0.56  thf('54', plain, ($false),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['36', '53'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
