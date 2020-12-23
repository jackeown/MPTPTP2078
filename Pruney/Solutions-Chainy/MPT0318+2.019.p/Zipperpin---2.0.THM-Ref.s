%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3sYCapOikV

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:23 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 525 expanded)
%              Number of leaves         :   25 ( 164 expanded)
%              Depth                    :   29
%              Number of atoms          :  808 (4107 expanded)
%              Number of equality atoms :   71 ( 415 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('0',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X41: $i,X42: $i,X45: $i] :
      ( ( X45
        = ( k2_zfmisc_1 @ X42 @ X41 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X45 @ X41 @ X42 ) @ ( sk_E @ X45 @ X41 @ X42 ) @ ( sk_D @ X45 @ X41 @ X42 ) @ X41 @ X42 )
      | ( r2_hidden @ ( sk_D @ X45 @ X41 @ X42 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X33 @ X35 )
      | ~ ( zip_tseitin_0 @ X33 @ X32 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(t130_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != k1_xboole_0 )
       => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
           != k1_xboole_0 )
          & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_zfmisc_1])).

thf('13',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('16',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('17',plain,(
    ! [X48: $i,X49: $i,X50: $i,X52: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X48 @ X50 ) @ ( k2_zfmisc_1 @ X49 @ ( k1_tarski @ X52 ) ) )
      | ( X50 != X52 )
      | ~ ( r2_hidden @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('18',plain,(
    ! [X48: $i,X49: $i,X52: $i] :
      ( ~ ( r2_hidden @ X48 @ X49 )
      | ( r2_hidden @ ( k4_tarski @ X48 @ X52 ) @ ( k2_zfmisc_1 @ X49 @ ( k1_tarski @ X52 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ X1 ) @ ( k2_zfmisc_1 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A_1 ) @ sk_B_1 ) @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A_1 ) )
   <= ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_A_1 != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A_1 ) @ sk_B_1 ) @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf('29',plain,(
    ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('31',plain,
    ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['14','31'])).

thf('33',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X33 @ X32 @ X34 @ X35 @ X37 )
      | ~ ( r2_hidden @ X32 @ X37 )
      | ~ ( r2_hidden @ X33 @ X35 )
      | ( X34
       != ( k4_tarski @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('36',plain,(
    ! [X32: $i,X33: $i,X35: $i,X37: $i] :
      ( ~ ( r2_hidden @ X33 @ X35 )
      | ~ ( r2_hidden @ X32 @ X37 )
      | ( zip_tseitin_0 @ X33 @ X32 @ ( k4_tarski @ X32 @ X33 ) @ X35 @ X37 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ ( sk_B @ X0 ) @ X2 @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ ( sk_B @ X1 ) @ ( sk_B @ X0 ) @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ X1 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 )
      | ( r2_hidden @ X40 @ X43 )
      | ( X43
       != ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( r2_hidden @ X40 @ ( k2_zfmisc_1 @ X42 @ X41 ) )
      | ~ ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A_1 )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_A_1 )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('48',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('50',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('51',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('52',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('54',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X50 = X51 )
      | ~ ( r2_hidden @ ( k4_tarski @ X48 @ X50 ) @ ( k2_zfmisc_1 @ X49 @ ( k1_tarski @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['55'])).

thf('57',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ X1 ) @ ( k2_zfmisc_1 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('62',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('63',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('64',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X50 = X51 )
      | ~ ( r2_hidden @ ( k4_tarski @ X48 @ X50 ) @ ( k2_zfmisc_1 @ X49 @ ( k1_tarski @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( X1 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X2 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( X0 = sk_B_1 )
      | ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X0 = sk_B_1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ X1 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['51','68'])).

thf('70',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = sk_B_1 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A_1 != X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) )
      | ( X1 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X1: $i] :
      ( ( X1 = sk_B_1 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X48: $i,X49: $i,X52: $i] :
      ( ~ ( r2_hidden @ X48 @ X49 )
      | ( r2_hidden @ ( k4_tarski @ X48 @ X52 ) @ ( k2_zfmisc_1 @ X49 @ ( k1_tarski @ X52 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['50','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_B_1 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf('83',plain,(
    ! [X0: $i] : ( X0 = sk_B_1 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X0: $i] : ( X0 = sk_B_1 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] : ( X1 = X0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('87',plain,(
    ! [X0: $i] : ( sk_A_1 != X0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    $false ),
    inference(simplify,[status(thm)],['87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3sYCapOikV
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.93/2.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.93/2.14  % Solved by: fo/fo7.sh
% 1.93/2.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.93/2.14  % done 1128 iterations in 1.654s
% 1.93/2.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.93/2.14  % SZS output start Refutation
% 1.93/2.14  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.93/2.14  thf(sk_A_type, type, sk_A: $i).
% 1.93/2.14  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 1.93/2.14  thf(sk_A_1_type, type, sk_A_1: $i).
% 1.93/2.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.93/2.14  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.93/2.14  thf(sk_B_type, type, sk_B: $i > $i).
% 1.93/2.14  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.93/2.14  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.93/2.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.93/2.14  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 1.93/2.14  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 1.93/2.14  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.93/2.14  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.93/2.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.93/2.14  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 1.93/2.14  thf('0', plain, ((v1_xboole_0 @ sk_A)),
% 1.93/2.14      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 1.93/2.14  thf('1', plain, ((v1_xboole_0 @ sk_A)),
% 1.93/2.14      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 1.93/2.14  thf(l13_xboole_0, axiom,
% 1.93/2.14    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.93/2.14  thf('2', plain,
% 1.93/2.14      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.93/2.14      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.93/2.14  thf('3', plain, (((sk_A) = (k1_xboole_0))),
% 1.93/2.14      inference('sup-', [status(thm)], ['1', '2'])).
% 1.93/2.14  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.93/2.14      inference('demod', [status(thm)], ['0', '3'])).
% 1.93/2.14  thf(d2_zfmisc_1, axiom,
% 1.93/2.14    (![A:$i,B:$i,C:$i]:
% 1.93/2.14     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 1.93/2.14       ( ![D:$i]:
% 1.93/2.14         ( ( r2_hidden @ D @ C ) <=>
% 1.93/2.14           ( ?[E:$i,F:$i]:
% 1.93/2.14             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 1.93/2.14               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 1.93/2.14  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 1.93/2.14  thf(zf_stmt_1, axiom,
% 1.93/2.14    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 1.93/2.14     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 1.93/2.14       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 1.93/2.14         ( r2_hidden @ E @ A ) ) ))).
% 1.93/2.14  thf(zf_stmt_2, axiom,
% 1.93/2.14    (![A:$i,B:$i,C:$i]:
% 1.93/2.14     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 1.93/2.14       ( ![D:$i]:
% 1.93/2.14         ( ( r2_hidden @ D @ C ) <=>
% 1.93/2.14           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 1.93/2.14  thf('5', plain,
% 1.93/2.14      (![X41 : $i, X42 : $i, X45 : $i]:
% 1.93/2.14         (((X45) = (k2_zfmisc_1 @ X42 @ X41))
% 1.93/2.14          | (zip_tseitin_0 @ (sk_F @ X45 @ X41 @ X42) @ 
% 1.93/2.14             (sk_E @ X45 @ X41 @ X42) @ (sk_D @ X45 @ X41 @ X42) @ X41 @ X42)
% 1.93/2.14          | (r2_hidden @ (sk_D @ X45 @ X41 @ X42) @ X45))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.93/2.14  thf('6', plain,
% 1.93/2.14      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.93/2.14         ((r2_hidden @ X33 @ X35)
% 1.93/2.14          | ~ (zip_tseitin_0 @ X33 @ X32 @ X34 @ X35 @ X36))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.93/2.14  thf('7', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.14         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 1.93/2.14          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 1.93/2.14          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 1.93/2.14      inference('sup-', [status(thm)], ['5', '6'])).
% 1.93/2.14  thf(d1_xboole_0, axiom,
% 1.93/2.14    (![A:$i]:
% 1.93/2.14     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.93/2.14  thf('8', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.93/2.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.93/2.14  thf('9', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.14         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 1.93/2.14          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 1.93/2.14          | ~ (v1_xboole_0 @ X0))),
% 1.93/2.14      inference('sup-', [status(thm)], ['7', '8'])).
% 1.93/2.14  thf('10', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.93/2.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.93/2.14  thf('11', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.14         (~ (v1_xboole_0 @ X2)
% 1.93/2.14          | ((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 1.93/2.14          | ~ (v1_xboole_0 @ X0))),
% 1.93/2.14      inference('sup-', [status(thm)], ['9', '10'])).
% 1.93/2.14  thf('12', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['4', '11'])).
% 1.93/2.14  thf(t130_zfmisc_1, conjecture,
% 1.93/2.14    (![A:$i,B:$i]:
% 1.93/2.14     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 1.93/2.14       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 1.93/2.14         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 1.93/2.14  thf(zf_stmt_3, negated_conjecture,
% 1.93/2.14    (~( ![A:$i,B:$i]:
% 1.93/2.14        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 1.93/2.14          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 1.93/2.14            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 1.93/2.14    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 1.93/2.14  thf('13', plain,
% 1.93/2.14      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0))
% 1.93/2.14        | ((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.93/2.14  thf('14', plain,
% 1.93/2.14      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0)))
% 1.93/2.14         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0))))),
% 1.93/2.14      inference('split', [status(esa)], ['13'])).
% 1.93/2.14  thf('15', plain,
% 1.93/2.14      ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))
% 1.93/2.14         <= ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 1.93/2.14      inference('split', [status(esa)], ['13'])).
% 1.93/2.14  thf('16', plain,
% 1.93/2.14      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.93/2.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.93/2.14  thf(t129_zfmisc_1, axiom,
% 1.93/2.14    (![A:$i,B:$i,C:$i,D:$i]:
% 1.93/2.14     ( ( r2_hidden @
% 1.93/2.14         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 1.93/2.14       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 1.93/2.14  thf('17', plain,
% 1.93/2.14      (![X48 : $i, X49 : $i, X50 : $i, X52 : $i]:
% 1.93/2.14         ((r2_hidden @ (k4_tarski @ X48 @ X50) @ 
% 1.93/2.14           (k2_zfmisc_1 @ X49 @ (k1_tarski @ X52)))
% 1.93/2.14          | ((X50) != (X52))
% 1.93/2.14          | ~ (r2_hidden @ X48 @ X49))),
% 1.93/2.14      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 1.93/2.14  thf('18', plain,
% 1.93/2.14      (![X48 : $i, X49 : $i, X52 : $i]:
% 1.93/2.14         (~ (r2_hidden @ X48 @ X49)
% 1.93/2.14          | (r2_hidden @ (k4_tarski @ X48 @ X52) @ 
% 1.93/2.14             (k2_zfmisc_1 @ X49 @ (k1_tarski @ X52))))),
% 1.93/2.14      inference('simplify', [status(thm)], ['17'])).
% 1.93/2.14  thf('19', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v1_xboole_0 @ X0)
% 1.93/2.14          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ X1) @ 
% 1.93/2.14             (k2_zfmisc_1 @ X0 @ (k1_tarski @ X1))))),
% 1.93/2.14      inference('sup-', [status(thm)], ['16', '18'])).
% 1.93/2.14  thf('20', plain,
% 1.93/2.14      ((((r2_hidden @ (k4_tarski @ (sk_B @ sk_A_1) @ sk_B_1) @ k1_xboole_0)
% 1.93/2.14         | (v1_xboole_0 @ sk_A_1)))
% 1.93/2.14         <= ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 1.93/2.14      inference('sup+', [status(thm)], ['15', '19'])).
% 1.93/2.14  thf('21', plain,
% 1.93/2.14      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.93/2.14      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.93/2.14  thf('22', plain, (((sk_A_1) != (k1_xboole_0))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.93/2.14  thf('23', plain, (![X0 : $i]: (((sk_A_1) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.93/2.14      inference('sup-', [status(thm)], ['21', '22'])).
% 1.93/2.14  thf('24', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 1.93/2.14      inference('simplify', [status(thm)], ['23'])).
% 1.93/2.14  thf('25', plain,
% 1.93/2.14      (((r2_hidden @ (k4_tarski @ (sk_B @ sk_A_1) @ sk_B_1) @ k1_xboole_0))
% 1.93/2.14         <= ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 1.93/2.14      inference('clc', [status(thm)], ['20', '24'])).
% 1.93/2.14  thf('26', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.93/2.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.93/2.14  thf('27', plain,
% 1.93/2.14      ((~ (v1_xboole_0 @ k1_xboole_0))
% 1.93/2.14         <= ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 1.93/2.14      inference('sup-', [status(thm)], ['25', '26'])).
% 1.93/2.14  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.93/2.14      inference('demod', [status(thm)], ['0', '3'])).
% 1.93/2.14  thf('29', plain,
% 1.93/2.14      (~ (((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 1.93/2.14      inference('demod', [status(thm)], ['27', '28'])).
% 1.93/2.14  thf('30', plain,
% 1.93/2.14      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0))) | 
% 1.93/2.14       (((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 1.93/2.14      inference('split', [status(esa)], ['13'])).
% 1.93/2.14  thf('31', plain,
% 1.93/2.14      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0)))),
% 1.93/2.14      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 1.93/2.14  thf('32', plain,
% 1.93/2.14      (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0))),
% 1.93/2.14      inference('simpl_trail', [status(thm)], ['14', '31'])).
% 1.93/2.14  thf('33', plain,
% 1.93/2.14      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.93/2.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.93/2.14  thf('34', plain,
% 1.93/2.14      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.93/2.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.93/2.14  thf('35', plain,
% 1.93/2.14      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X37 : $i]:
% 1.93/2.14         ((zip_tseitin_0 @ X33 @ X32 @ X34 @ X35 @ X37)
% 1.93/2.14          | ~ (r2_hidden @ X32 @ X37)
% 1.93/2.14          | ~ (r2_hidden @ X33 @ X35)
% 1.93/2.14          | ((X34) != (k4_tarski @ X32 @ X33)))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.93/2.14  thf('36', plain,
% 1.93/2.14      (![X32 : $i, X33 : $i, X35 : $i, X37 : $i]:
% 1.93/2.14         (~ (r2_hidden @ X33 @ X35)
% 1.93/2.14          | ~ (r2_hidden @ X32 @ X37)
% 1.93/2.14          | (zip_tseitin_0 @ X33 @ X32 @ (k4_tarski @ X32 @ X33) @ X35 @ X37))),
% 1.93/2.14      inference('simplify', [status(thm)], ['35'])).
% 1.93/2.14  thf('37', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.14         ((v1_xboole_0 @ X0)
% 1.93/2.14          | (zip_tseitin_0 @ (sk_B @ X0) @ X2 @ 
% 1.93/2.14             (k4_tarski @ X2 @ (sk_B @ X0)) @ X0 @ X1)
% 1.93/2.14          | ~ (r2_hidden @ X2 @ X1))),
% 1.93/2.14      inference('sup-', [status(thm)], ['34', '36'])).
% 1.93/2.14  thf('38', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v1_xboole_0 @ X0)
% 1.93/2.14          | (zip_tseitin_0 @ (sk_B @ X1) @ (sk_B @ X0) @ 
% 1.93/2.14             (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ X1 @ X0)
% 1.93/2.14          | (v1_xboole_0 @ X1))),
% 1.93/2.14      inference('sup-', [status(thm)], ['33', '37'])).
% 1.93/2.14  thf('39', plain,
% 1.93/2.14      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.93/2.14         (~ (zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42)
% 1.93/2.14          | (r2_hidden @ X40 @ X43)
% 1.93/2.14          | ((X43) != (k2_zfmisc_1 @ X42 @ X41)))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.93/2.14  thf('40', plain,
% 1.93/2.14      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.93/2.14         ((r2_hidden @ X40 @ (k2_zfmisc_1 @ X42 @ X41))
% 1.93/2.14          | ~ (zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 1.93/2.14      inference('simplify', [status(thm)], ['39'])).
% 1.93/2.14  thf('41', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v1_xboole_0 @ X1)
% 1.93/2.14          | (v1_xboole_0 @ X0)
% 1.93/2.14          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 1.93/2.14             (k2_zfmisc_1 @ X0 @ X1)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['38', '40'])).
% 1.93/2.14  thf('42', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.93/2.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.93/2.14  thf('43', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v1_xboole_0 @ X1)
% 1.93/2.14          | (v1_xboole_0 @ X0)
% 1.93/2.14          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['41', '42'])).
% 1.93/2.14  thf('44', plain,
% 1.93/2.14      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.93/2.14        | (v1_xboole_0 @ sk_A_1)
% 1.93/2.14        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['32', '43'])).
% 1.93/2.14  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.93/2.14      inference('demod', [status(thm)], ['0', '3'])).
% 1.93/2.14  thf('46', plain,
% 1.93/2.14      (((v1_xboole_0 @ sk_A_1) | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 1.93/2.14      inference('demod', [status(thm)], ['44', '45'])).
% 1.93/2.14  thf('47', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 1.93/2.14      inference('simplify', [status(thm)], ['23'])).
% 1.93/2.14  thf('48', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B_1))),
% 1.93/2.14      inference('clc', [status(thm)], ['46', '47'])).
% 1.93/2.14  thf('49', plain,
% 1.93/2.14      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.93/2.14      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.93/2.14  thf('50', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 1.93/2.14      inference('sup-', [status(thm)], ['48', '49'])).
% 1.93/2.14  thf(t69_enumset1, axiom,
% 1.93/2.14    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.93/2.14  thf('51', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 1.93/2.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.93/2.14  thf('52', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 1.93/2.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.93/2.14  thf('53', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v1_xboole_0 @ X1)
% 1.93/2.14          | (v1_xboole_0 @ X0)
% 1.93/2.14          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 1.93/2.14             (k2_zfmisc_1 @ X0 @ X1)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['38', '40'])).
% 1.93/2.14  thf('54', plain,
% 1.93/2.14      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.93/2.14         (((X50) = (X51))
% 1.93/2.14          | ~ (r2_hidden @ (k4_tarski @ X48 @ X50) @ 
% 1.93/2.14               (k2_zfmisc_1 @ X49 @ (k1_tarski @ X51))))),
% 1.93/2.14      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 1.93/2.14  thf('55', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v1_xboole_0 @ X1)
% 1.93/2.14          | (v1_xboole_0 @ (k1_tarski @ X0))
% 1.93/2.14          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['53', '54'])).
% 1.93/2.14  thf('56', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (((sk_B @ (k1_tarski @ X0)) = (X0)) | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 1.93/2.14      inference('condensation', [status(thm)], ['55'])).
% 1.93/2.14  thf('57', plain,
% 1.93/2.14      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.93/2.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.93/2.14  thf('58', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.93/2.14          | (v1_xboole_0 @ (k1_tarski @ X0))
% 1.93/2.14          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 1.93/2.14      inference('sup+', [status(thm)], ['56', '57'])).
% 1.93/2.14  thf('59', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((v1_xboole_0 @ (k1_tarski @ X0))
% 1.93/2.14          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.93/2.14      inference('simplify', [status(thm)], ['58'])).
% 1.93/2.14  thf('60', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))
% 1.93/2.14          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 1.93/2.14      inference('sup+', [status(thm)], ['52', '59'])).
% 1.93/2.14  thf('61', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v1_xboole_0 @ X0)
% 1.93/2.14          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ X1) @ 
% 1.93/2.14             (k2_zfmisc_1 @ X0 @ (k1_tarski @ X1))))),
% 1.93/2.14      inference('sup-', [status(thm)], ['16', '18'])).
% 1.93/2.14  thf('62', plain,
% 1.93/2.14      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.93/2.14      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.93/2.14  thf('63', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 1.93/2.14      inference('sup-', [status(thm)], ['48', '49'])).
% 1.93/2.14  thf('64', plain,
% 1.93/2.14      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.93/2.14         (((X50) = (X51))
% 1.93/2.14          | ~ (r2_hidden @ (k4_tarski @ X48 @ X50) @ 
% 1.93/2.14               (k2_zfmisc_1 @ X49 @ (k1_tarski @ X51))))),
% 1.93/2.14      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 1.93/2.14  thf('65', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.14         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ 
% 1.93/2.14             (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 1.93/2.14          | ((X1) = (sk_B_1)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['63', '64'])).
% 1.93/2.14  thf('66', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.93/2.14         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0))
% 1.93/2.14          | ~ (v1_xboole_0 @ X0)
% 1.93/2.14          | ((X2) = (sk_B_1)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['62', '65'])).
% 1.93/2.14  thf('67', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v1_xboole_0 @ X1)
% 1.93/2.14          | ((X0) = (sk_B_1))
% 1.93/2.14          | ~ (v1_xboole_0 @ (k1_tarski @ X0)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['61', '66'])).
% 1.93/2.14  thf('68', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))
% 1.93/2.14          | ((X0) = (sk_B_1))
% 1.93/2.14          | (v1_xboole_0 @ X1))),
% 1.93/2.14      inference('sup-', [status(thm)], ['60', '67'])).
% 1.93/2.14  thf('69', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.93/2.14          | (v1_xboole_0 @ X1)
% 1.93/2.14          | ((X0) = (sk_B_1)))),
% 1.93/2.14      inference('sup+', [status(thm)], ['51', '68'])).
% 1.93/2.14  thf('70', plain,
% 1.93/2.14      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.93/2.14      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.93/2.14  thf('71', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         (((X1) = (sk_B_1))
% 1.93/2.14          | (r2_hidden @ X1 @ (k1_tarski @ X1))
% 1.93/2.14          | ((X0) = (k1_xboole_0)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['69', '70'])).
% 1.93/2.14  thf('72', plain, (((sk_A_1) != (k1_xboole_0))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.93/2.14  thf('73', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         (((sk_A_1) != (X0))
% 1.93/2.14          | (r2_hidden @ X1 @ (k1_tarski @ X1))
% 1.93/2.14          | ((X1) = (sk_B_1)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['71', '72'])).
% 1.93/2.14  thf('74', plain,
% 1.93/2.14      (![X1 : $i]: (((X1) = (sk_B_1)) | (r2_hidden @ X1 @ (k1_tarski @ X1)))),
% 1.93/2.14      inference('simplify', [status(thm)], ['73'])).
% 1.93/2.14  thf('75', plain,
% 1.93/2.14      (![X48 : $i, X49 : $i, X52 : $i]:
% 1.93/2.14         (~ (r2_hidden @ X48 @ X49)
% 1.93/2.14          | (r2_hidden @ (k4_tarski @ X48 @ X52) @ 
% 1.93/2.14             (k2_zfmisc_1 @ X49 @ (k1_tarski @ X52))))),
% 1.93/2.14      inference('simplify', [status(thm)], ['17'])).
% 1.93/2.14  thf('76', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         (((X0) = (sk_B_1))
% 1.93/2.14          | (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 1.93/2.14             (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1))))),
% 1.93/2.14      inference('sup-', [status(thm)], ['74', '75'])).
% 1.93/2.14  thf('77', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_hidden @ (k4_tarski @ X0 @ sk_B_1) @ 
% 1.93/2.14           (k2_zfmisc_1 @ (k1_tarski @ X0) @ k1_xboole_0))
% 1.93/2.14          | ((X0) = (sk_B_1)))),
% 1.93/2.14      inference('sup+', [status(thm)], ['50', '76'])).
% 1.93/2.14  thf('78', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.93/2.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.93/2.14  thf('79', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (((X0) = (sk_B_1))
% 1.93/2.14          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X0) @ k1_xboole_0)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['77', '78'])).
% 1.93/2.14  thf('80', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.93/2.14          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.93/2.14          | ((X0) = (sk_B_1)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['12', '79'])).
% 1.93/2.14  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.93/2.14      inference('demod', [status(thm)], ['0', '3'])).
% 1.93/2.14  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.93/2.14      inference('demod', [status(thm)], ['0', '3'])).
% 1.93/2.14  thf('83', plain, (![X0 : $i]: ((X0) = (sk_B_1))),
% 1.93/2.14      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.93/2.14  thf('84', plain, (![X0 : $i]: ((X0) = (sk_B_1))),
% 1.93/2.14      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.93/2.14  thf('85', plain, (![X0 : $i, X1 : $i]: ((X1) = (X0))),
% 1.93/2.14      inference('sup+', [status(thm)], ['83', '84'])).
% 1.93/2.14  thf('86', plain, (((sk_A_1) != (k1_xboole_0))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.93/2.14  thf('87', plain, (![X0 : $i]: ((sk_A_1) != (X0))),
% 1.93/2.14      inference('sup-', [status(thm)], ['85', '86'])).
% 1.93/2.14  thf('88', plain, ($false), inference('simplify', [status(thm)], ['87'])).
% 1.93/2.14  
% 1.93/2.14  % SZS output end Refutation
% 1.93/2.14  
% 1.93/2.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
