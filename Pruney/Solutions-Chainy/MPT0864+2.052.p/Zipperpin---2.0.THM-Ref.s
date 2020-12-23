%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pZPwzMZEtb

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:06 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 192 expanded)
%              Number of leaves         :   38 (  73 expanded)
%              Depth                    :   17
%              Number of atoms          :  676 (1725 expanded)
%              Number of equality atoms :   83 ( 196 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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
    ! [X88: $i,X90: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X88 @ X90 ) )
      = X90 ) ),
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
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('12',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
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
    zip_tseitin_1: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [H: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ H @ F @ E @ D @ C @ B @ A )
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
        <=> ~ ( zip_tseitin_1 @ H @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X78: $i,X79: $i,X80: $i,X81: $i,X82: $i,X83: $i,X84: $i,X85: $i] :
      ( ( zip_tseitin_1 @ X78 @ X79 @ X80 @ X81 @ X82 @ X83 @ X84 )
      | ( r2_hidden @ X78 @ X85 )
      | ( X85
       != ( k4_enumset1 @ X84 @ X83 @ X82 @ X81 @ X80 @ X79 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X78: $i,X79: $i,X80: $i,X81: $i,X82: $i,X83: $i,X84: $i] :
      ( ( r2_hidden @ X78 @ ( k4_enumset1 @ X84 @ X83 @ X82 @ X81 @ X80 @ X79 ) )
      | ( zip_tseitin_1 @ X78 @ X79 @ X80 @ X81 @ X82 @ X83 @ X84 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_1 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X70: $i,X71: $i,X72: $i,X73: $i,X74: $i,X75: $i,X76: $i] :
      ( ( X71 != X70 )
      | ~ ( zip_tseitin_1 @ X71 @ X72 @ X73 @ X74 @ X75 @ X76 @ X70 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    ! [X70: $i,X72: $i,X73: $i,X74: $i,X75: $i,X76: $i] :
      ~ ( zip_tseitin_1 @ X70 @ X72 @ X73 @ X74 @ X75 @ X76 @ X70 ) ),
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
    ! [X61: $i,X62: $i,X63: $i,X65: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X61 @ X63 ) @ ( k2_zfmisc_1 @ X62 @ X65 ) )
      | ~ ( r2_hidden @ X63 @ X65 )
      | ~ ( r2_hidden @ X61 @ X62 ) ) ),
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

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('28',plain,(
    ! [X56: $i,X58: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X56 ) @ X58 )
      | ~ ( r2_hidden @ X56 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('29',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X88: $i,X89: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X88 @ X89 ) )
      = X88 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('32',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('34',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X56: $i,X58: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X56 ) @ X58 )
      | ~ ( r2_hidden @ X56 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('40',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('41',plain,(
    ! [X66: $i,X67: $i] :
      ( ( X66 = k1_xboole_0 )
      | ~ ( r1_tarski @ X66 @ ( k2_zfmisc_1 @ X66 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('46',plain,(
    ! [X1: $i] :
      ( ( k5_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('48',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X68 ) @ X69 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['42','49'])).

thf('51',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('52',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['29','52'])).

thf('54',plain,(
    ! [X66: $i,X67: $i] :
      ( ( X66 = k1_xboole_0 )
      | ~ ( r1_tarski @ X66 @ ( k2_zfmisc_1 @ X67 @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('55',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pZPwzMZEtb
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.36/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.62  % Solved by: fo/fo7.sh
% 0.36/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.62  % done 362 iterations in 0.153s
% 0.36/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.62  % SZS output start Refutation
% 0.36/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.36/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.62  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.36/0.62  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.36/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.62  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.62  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.36/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.36/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.62  thf(t20_mcart_1, conjecture,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.36/0.62       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.36/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.62    (~( ![A:$i]:
% 0.36/0.62        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.36/0.62          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.36/0.62    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.36/0.62  thf('0', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(t7_mcart_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.36/0.62       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.36/0.62  thf('1', plain,
% 0.36/0.62      (![X88 : $i, X90 : $i]: ((k2_mcart_1 @ (k4_tarski @ X88 @ X90)) = (X90))),
% 0.36/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.36/0.62  thf('2', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.36/0.62      inference('sup+', [status(thm)], ['0', '1'])).
% 0.36/0.62  thf('3', plain,
% 0.36/0.62      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('4', plain,
% 0.36/0.62      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.36/0.62      inference('split', [status(esa)], ['3'])).
% 0.36/0.62  thf('5', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['2', '4'])).
% 0.36/0.62  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('7', plain,
% 0.36/0.62      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.36/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.62  thf(t70_enumset1, axiom,
% 0.36/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.62  thf('8', plain,
% 0.36/0.62      (![X29 : $i, X30 : $i]:
% 0.36/0.62         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.36/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.62  thf(t69_enumset1, axiom,
% 0.36/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.62  thf('9', plain, (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.36/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.62  thf('10', plain,
% 0.36/0.62      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.62  thf(t71_enumset1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.36/0.62  thf('11', plain,
% 0.36/0.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.62         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 0.36/0.62           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 0.36/0.62      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.36/0.62  thf(t72_enumset1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.62     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.36/0.62  thf('12', plain,
% 0.36/0.62      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.36/0.62         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 0.36/0.62           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 0.36/0.62      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.36/0.62  thf(t73_enumset1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.62     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.36/0.62       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.36/0.62  thf('13', plain,
% 0.36/0.62      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.36/0.62         ((k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.36/0.62           = (k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 0.36/0.62      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.36/0.62  thf(d4_enumset1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.36/0.62     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.36/0.62       ( ![H:$i]:
% 0.36/0.62         ( ( r2_hidden @ H @ G ) <=>
% 0.36/0.62           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.36/0.62                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.36/0.62  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.36/0.62  thf(zf_stmt_2, axiom,
% 0.36/0.62    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.36/0.62     ( ( zip_tseitin_1 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.36/0.62       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.36/0.62         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.36/0.62  thf(zf_stmt_3, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.36/0.62     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.36/0.62       ( ![H:$i]:
% 0.36/0.62         ( ( r2_hidden @ H @ G ) <=>
% 0.36/0.62           ( ~( zip_tseitin_1 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.36/0.62  thf('14', plain,
% 0.36/0.62      (![X78 : $i, X79 : $i, X80 : $i, X81 : $i, X82 : $i, X83 : $i, X84 : $i, 
% 0.36/0.62         X85 : $i]:
% 0.36/0.62         ((zip_tseitin_1 @ X78 @ X79 @ X80 @ X81 @ X82 @ X83 @ X84)
% 0.36/0.62          | (r2_hidden @ X78 @ X85)
% 0.36/0.62          | ((X85) != (k4_enumset1 @ X84 @ X83 @ X82 @ X81 @ X80 @ X79)))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.62  thf('15', plain,
% 0.36/0.62      (![X78 : $i, X79 : $i, X80 : $i, X81 : $i, X82 : $i, X83 : $i, X84 : $i]:
% 0.36/0.62         ((r2_hidden @ X78 @ (k4_enumset1 @ X84 @ X83 @ X82 @ X81 @ X80 @ X79))
% 0.36/0.62          | (zip_tseitin_1 @ X78 @ X79 @ X80 @ X81 @ X82 @ X83 @ X84))),
% 0.36/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.36/0.62  thf('16', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.62         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.62          | (zip_tseitin_1 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.36/0.62      inference('sup+', [status(thm)], ['13', '15'])).
% 0.36/0.62  thf('17', plain,
% 0.36/0.62      (![X70 : $i, X71 : $i, X72 : $i, X73 : $i, X74 : $i, X75 : $i, X76 : $i]:
% 0.36/0.62         (((X71) != (X70))
% 0.36/0.62          | ~ (zip_tseitin_1 @ X71 @ X72 @ X73 @ X74 @ X75 @ X76 @ X70))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.62  thf('18', plain,
% 0.36/0.62      (![X70 : $i, X72 : $i, X73 : $i, X74 : $i, X75 : $i, X76 : $i]:
% 0.36/0.62         ~ (zip_tseitin_1 @ X70 @ X72 @ X73 @ X74 @ X75 @ X76 @ X70)),
% 0.36/0.62      inference('simplify', [status(thm)], ['17'])).
% 0.36/0.62  thf('19', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.62         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.36/0.62      inference('sup-', [status(thm)], ['16', '18'])).
% 0.36/0.62  thf('20', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.62         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['12', '19'])).
% 0.36/0.62  thf('21', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.62         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['11', '20'])).
% 0.36/0.62  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['10', '21'])).
% 0.36/0.62  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['10', '21'])).
% 0.36/0.62  thf(l54_zfmisc_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.62     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.36/0.62       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.36/0.62  thf('24', plain,
% 0.36/0.62      (![X61 : $i, X62 : $i, X63 : $i, X65 : $i]:
% 0.36/0.62         ((r2_hidden @ (k4_tarski @ X61 @ X63) @ (k2_zfmisc_1 @ X62 @ X65))
% 0.36/0.62          | ~ (r2_hidden @ X63 @ X65)
% 0.36/0.62          | ~ (r2_hidden @ X61 @ X62))),
% 0.36/0.62      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.36/0.62  thf('25', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.62         (~ (r2_hidden @ X2 @ X1)
% 0.36/0.62          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.36/0.62             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.62  thf('26', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.36/0.62          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.62  thf('27', plain,
% 0.36/0.62      (((r2_hidden @ sk_A @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))
% 0.36/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['7', '26'])).
% 0.36/0.62  thf(l1_zfmisc_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.36/0.62  thf('28', plain,
% 0.36/0.62      (![X56 : $i, X58 : $i]:
% 0.36/0.62         ((r1_tarski @ (k1_tarski @ X56) @ X58) | ~ (r2_hidden @ X56 @ X58))),
% 0.36/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.36/0.62  thf('29', plain,
% 0.36/0.62      (((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))
% 0.36/0.62         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.62  thf('30', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('31', plain,
% 0.36/0.62      (![X88 : $i, X89 : $i]: ((k1_mcart_1 @ (k4_tarski @ X88 @ X89)) = (X88))),
% 0.36/0.62      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.36/0.62  thf('32', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['30', '31'])).
% 0.36/0.62  thf('33', plain,
% 0.36/0.62      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.36/0.62      inference('split', [status(esa)], ['3'])).
% 0.36/0.62  thf('34', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['32', '33'])).
% 0.36/0.62  thf('35', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('36', plain,
% 0.36/0.62      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.36/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['34', '35'])).
% 0.36/0.62  thf('37', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.36/0.62          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.62  thf('38', plain,
% 0.36/0.62      (((r2_hidden @ sk_A @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))))
% 0.36/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['36', '37'])).
% 0.36/0.62  thf('39', plain,
% 0.36/0.62      (![X56 : $i, X58 : $i]:
% 0.36/0.62         ((r1_tarski @ (k1_tarski @ X56) @ X58) | ~ (r2_hidden @ X56 @ X58))),
% 0.36/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.36/0.62  thf('40', plain,
% 0.36/0.62      (((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))))
% 0.36/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.62  thf(t135_zfmisc_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.36/0.62         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.36/0.62       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.62  thf('41', plain,
% 0.36/0.62      (![X66 : $i, X67 : $i]:
% 0.36/0.62         (((X66) = (k1_xboole_0))
% 0.36/0.62          | ~ (r1_tarski @ X66 @ (k2_zfmisc_1 @ X66 @ X67)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.36/0.62  thf('42', plain,
% 0.36/0.62      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.36/0.62         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.62  thf(t4_boole, axiom,
% 0.36/0.62    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.62  thf('43', plain,
% 0.36/0.62      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.62      inference('cnf', [status(esa)], [t4_boole])).
% 0.36/0.62  thf(t98_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.36/0.62  thf('44', plain,
% 0.36/0.62      (![X2 : $i, X3 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X2 @ X3)
% 0.36/0.62           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.62  thf('45', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['43', '44'])).
% 0.36/0.62  thf(t5_boole, axiom,
% 0.36/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.62  thf('46', plain, (![X1 : $i]: ((k5_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.62  thf('47', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['45', '46'])).
% 0.36/0.62  thf(t49_zfmisc_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.36/0.62  thf('48', plain,
% 0.36/0.62      (![X68 : $i, X69 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ (k1_tarski @ X68) @ X69) != (k1_xboole_0))),
% 0.36/0.62      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.36/0.62  thf('49', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.62  thf('50', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.36/0.62      inference('simplify_reflect-', [status(thm)], ['42', '49'])).
% 0.36/0.62  thf('51', plain,
% 0.36/0.62      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.36/0.62      inference('split', [status(esa)], ['3'])).
% 0.36/0.62  thf('52', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.36/0.62      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.36/0.62  thf('53', plain,
% 0.36/0.62      ((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.36/0.62        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.36/0.62      inference('simpl_trail', [status(thm)], ['29', '52'])).
% 0.36/0.62  thf('54', plain,
% 0.36/0.62      (![X66 : $i, X67 : $i]:
% 0.36/0.62         (((X66) = (k1_xboole_0))
% 0.36/0.62          | ~ (r1_tarski @ X66 @ (k2_zfmisc_1 @ X67 @ X66)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.36/0.62  thf('55', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.62  thf('56', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.62  thf('57', plain, ($false),
% 0.36/0.62      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 0.36/0.62  
% 0.36/0.62  % SZS output end Refutation
% 0.36/0.62  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
