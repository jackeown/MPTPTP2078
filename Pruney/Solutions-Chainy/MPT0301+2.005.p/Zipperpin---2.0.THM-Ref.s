%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IUXewTrG3X

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:59 EST 2020

% Result     : Theorem 12.08s
% Output     : Refutation 12.08s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 157 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  681 (1378 expanded)
%              Number of equality atoms :  107 ( 230 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t113_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
      <=> ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_zfmisc_1])).

thf('0',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X53 @ X52 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X53 @ X50 @ X51 ) @ ( sk_E_1 @ X53 @ X50 @ X51 ) @ X53 @ X50 @ X51 )
      | ( X52
       != ( k2_zfmisc_1 @ X51 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X50: $i,X51: $i,X53: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X53 @ X50 @ X51 ) @ ( sk_E_1 @ X53 @ X50 @ X51 ) @ X53 @ X50 @ X51 )
      | ~ ( r2_hidden @ X53 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( r2_hidden @ X42 @ X44 )
      | ~ ( zip_tseitin_0 @ X42 @ X41 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('11',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('18',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('27',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('30',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('31',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('32',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('33',plain,(
    ! [X59: $i,X60: $i,X61: $i,X63: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X59 @ X61 ) @ ( k2_zfmisc_1 @ X60 @ X63 ) )
      | ~ ( r2_hidden @ X61 @ X63 )
      | ~ ( r2_hidden @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('38',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('43',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('46',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( r2_hidden @ X41 @ X45 )
      | ~ ( zip_tseitin_0 @ X42 @ X41 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('49',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('50',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('55',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('57',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('60',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','28','29','44','58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IUXewTrG3X
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:54:03 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 12.08/12.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.08/12.27  % Solved by: fo/fo7.sh
% 12.08/12.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.08/12.27  % done 3940 iterations in 11.830s
% 12.08/12.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.08/12.27  % SZS output start Refutation
% 12.08/12.27  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 12.08/12.27  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 12.08/12.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.08/12.27  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 12.08/12.27  thf(sk_B_type, type, sk_B: $i > $i).
% 12.08/12.27  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 12.08/12.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.08/12.27  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 12.08/12.27  thf(sk_B_1_type, type, sk_B_1: $i).
% 12.08/12.27  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 12.08/12.27  thf(sk_A_type, type, sk_A: $i).
% 12.08/12.27  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 12.08/12.27  thf(t113_zfmisc_1, conjecture,
% 12.08/12.27    (![A:$i,B:$i]:
% 12.08/12.27     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 12.08/12.27       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 12.08/12.27  thf(zf_stmt_0, negated_conjecture,
% 12.08/12.27    (~( ![A:$i,B:$i]:
% 12.08/12.27        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 12.08/12.27          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 12.08/12.27    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 12.08/12.27  thf('0', plain,
% 12.08/12.27      ((((sk_B_1) != (k1_xboole_0))
% 12.08/12.27        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 12.08/12.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.08/12.27  thf('1', plain,
% 12.08/12.27      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 12.08/12.27       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 12.08/12.27      inference('split', [status(esa)], ['0'])).
% 12.08/12.27  thf(t7_xboole_0, axiom,
% 12.08/12.27    (![A:$i]:
% 12.08/12.27     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 12.08/12.27          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 12.08/12.27  thf('2', plain,
% 12.08/12.27      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 12.08/12.27      inference('cnf', [status(esa)], [t7_xboole_0])).
% 12.08/12.27  thf(d2_zfmisc_1, axiom,
% 12.08/12.27    (![A:$i,B:$i,C:$i]:
% 12.08/12.27     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 12.08/12.27       ( ![D:$i]:
% 12.08/12.27         ( ( r2_hidden @ D @ C ) <=>
% 12.08/12.27           ( ?[E:$i,F:$i]:
% 12.08/12.27             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 12.08/12.27               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 12.08/12.27  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 12.08/12.27  thf(zf_stmt_2, axiom,
% 12.08/12.27    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 12.08/12.27     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 12.08/12.27       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 12.08/12.27         ( r2_hidden @ E @ A ) ) ))).
% 12.08/12.27  thf(zf_stmt_3, axiom,
% 12.08/12.27    (![A:$i,B:$i,C:$i]:
% 12.08/12.27     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 12.08/12.27       ( ![D:$i]:
% 12.08/12.27         ( ( r2_hidden @ D @ C ) <=>
% 12.08/12.27           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 12.08/12.27  thf('3', plain,
% 12.08/12.27      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 12.08/12.27         (~ (r2_hidden @ X53 @ X52)
% 12.08/12.27          | (zip_tseitin_0 @ (sk_F_1 @ X53 @ X50 @ X51) @ 
% 12.08/12.27             (sk_E_1 @ X53 @ X50 @ X51) @ X53 @ X50 @ X51)
% 12.08/12.27          | ((X52) != (k2_zfmisc_1 @ X51 @ X50)))),
% 12.08/12.27      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.08/12.27  thf('4', plain,
% 12.08/12.27      (![X50 : $i, X51 : $i, X53 : $i]:
% 12.08/12.27         ((zip_tseitin_0 @ (sk_F_1 @ X53 @ X50 @ X51) @ 
% 12.08/12.27           (sk_E_1 @ X53 @ X50 @ X51) @ X53 @ X50 @ X51)
% 12.08/12.27          | ~ (r2_hidden @ X53 @ (k2_zfmisc_1 @ X51 @ X50)))),
% 12.08/12.27      inference('simplify', [status(thm)], ['3'])).
% 12.08/12.27  thf('5', plain,
% 12.08/12.27      (![X0 : $i, X1 : $i]:
% 12.08/12.27         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 12.08/12.27          | (zip_tseitin_0 @ 
% 12.08/12.27             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 12.08/12.27             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 12.08/12.27             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 12.08/12.27      inference('sup-', [status(thm)], ['2', '4'])).
% 12.08/12.27  thf('6', plain,
% 12.08/12.27      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 12.08/12.27         ((r2_hidden @ X42 @ X44)
% 12.08/12.27          | ~ (zip_tseitin_0 @ X42 @ X41 @ X43 @ X44 @ X45))),
% 12.08/12.27      inference('cnf', [status(esa)], [zf_stmt_2])).
% 12.08/12.27  thf('7', plain,
% 12.08/12.27      (![X0 : $i, X1 : $i]:
% 12.08/12.27         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 12.08/12.27          | (r2_hidden @ 
% 12.08/12.27             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X1))),
% 12.08/12.27      inference('sup-', [status(thm)], ['5', '6'])).
% 12.08/12.27  thf('8', plain,
% 12.08/12.27      ((((sk_B_1) = (k1_xboole_0))
% 12.08/12.27        | ((sk_A) = (k1_xboole_0))
% 12.08/12.27        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 12.08/12.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.08/12.27  thf('9', plain,
% 12.08/12.27      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('split', [status(esa)], ['8'])).
% 12.08/12.27  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 12.08/12.27  thf('10', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 12.08/12.27      inference('cnf', [status(esa)], [t65_xboole_1])).
% 12.08/12.27  thf('11', plain,
% 12.08/12.27      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 12.08/12.27      inference('cnf', [status(esa)], [t7_xboole_0])).
% 12.08/12.27  thf(t4_xboole_0, axiom,
% 12.08/12.27    (![A:$i,B:$i]:
% 12.08/12.27     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 12.08/12.27            ( r1_xboole_0 @ A @ B ) ) ) & 
% 12.08/12.27       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 12.08/12.27            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 12.08/12.27  thf('12', plain,
% 12.08/12.27      (![X2 : $i, X4 : $i, X5 : $i]:
% 12.08/12.27         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 12.08/12.27          | ~ (r1_xboole_0 @ X2 @ X5))),
% 12.08/12.27      inference('cnf', [status(esa)], [t4_xboole_0])).
% 12.08/12.27  thf('13', plain,
% 12.08/12.27      (![X0 : $i, X1 : $i]:
% 12.08/12.27         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 12.08/12.27      inference('sup-', [status(thm)], ['11', '12'])).
% 12.08/12.27  thf('14', plain,
% 12.08/12.27      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 12.08/12.27      inference('sup-', [status(thm)], ['10', '13'])).
% 12.08/12.27  thf('15', plain,
% 12.08/12.27      (![X2 : $i, X4 : $i, X5 : $i]:
% 12.08/12.27         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 12.08/12.27          | ~ (r1_xboole_0 @ X2 @ X5))),
% 12.08/12.27      inference('cnf', [status(esa)], [t4_xboole_0])).
% 12.08/12.27  thf('16', plain,
% 12.08/12.27      (![X0 : $i, X1 : $i]:
% 12.08/12.27         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 12.08/12.27      inference('sup-', [status(thm)], ['14', '15'])).
% 12.08/12.27  thf('17', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 12.08/12.27      inference('cnf', [status(esa)], [t65_xboole_1])).
% 12.08/12.27  thf('18', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 12.08/12.27      inference('demod', [status(thm)], ['16', '17'])).
% 12.08/12.27  thf('19', plain,
% 12.08/12.27      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1))
% 12.08/12.27         <= ((((sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('sup-', [status(thm)], ['9', '18'])).
% 12.08/12.27  thf('20', plain,
% 12.08/12.27      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0)))
% 12.08/12.27         <= ((((sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('sup-', [status(thm)], ['7', '19'])).
% 12.08/12.27  thf('21', plain,
% 12.08/12.27      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('split', [status(esa)], ['8'])).
% 12.08/12.27  thf('22', plain,
% 12.08/12.27      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_B_1) = (sk_B_1)))
% 12.08/12.27         <= ((((sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('demod', [status(thm)], ['20', '21'])).
% 12.08/12.27  thf('23', plain,
% 12.08/12.27      ((((sk_A) != (k1_xboole_0))
% 12.08/12.27        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 12.08/12.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.08/12.27  thf('24', plain,
% 12.08/12.27      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 12.08/12.27         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('split', [status(esa)], ['23'])).
% 12.08/12.27  thf('25', plain,
% 12.08/12.27      ((((sk_B_1) != (k1_xboole_0)))
% 12.08/12.27         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 12.08/12.27             (((sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('sup-', [status(thm)], ['22', '24'])).
% 12.08/12.27  thf('26', plain,
% 12.08/12.27      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('split', [status(esa)], ['8'])).
% 12.08/12.27  thf('27', plain,
% 12.08/12.27      ((((sk_B_1) != (sk_B_1)))
% 12.08/12.27         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 12.08/12.27             (((sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('demod', [status(thm)], ['25', '26'])).
% 12.08/12.27  thf('28', plain,
% 12.08/12.27      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 12.08/12.27       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 12.08/12.27      inference('simplify', [status(thm)], ['27'])).
% 12.08/12.27  thf('29', plain,
% 12.08/12.27      (~ (((sk_A) = (k1_xboole_0))) | 
% 12.08/12.27       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 12.08/12.27      inference('split', [status(esa)], ['23'])).
% 12.08/12.27  thf('30', plain,
% 12.08/12.27      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 12.08/12.27         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('split', [status(esa)], ['8'])).
% 12.08/12.27  thf('31', plain,
% 12.08/12.27      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 12.08/12.27      inference('cnf', [status(esa)], [t7_xboole_0])).
% 12.08/12.27  thf('32', plain,
% 12.08/12.27      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 12.08/12.27      inference('cnf', [status(esa)], [t7_xboole_0])).
% 12.08/12.27  thf(l54_zfmisc_1, axiom,
% 12.08/12.27    (![A:$i,B:$i,C:$i,D:$i]:
% 12.08/12.27     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 12.08/12.27       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 12.08/12.27  thf('33', plain,
% 12.08/12.27      (![X59 : $i, X60 : $i, X61 : $i, X63 : $i]:
% 12.08/12.27         ((r2_hidden @ (k4_tarski @ X59 @ X61) @ (k2_zfmisc_1 @ X60 @ X63))
% 12.08/12.27          | ~ (r2_hidden @ X61 @ X63)
% 12.08/12.27          | ~ (r2_hidden @ X59 @ X60))),
% 12.08/12.27      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 12.08/12.27  thf('34', plain,
% 12.08/12.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.08/12.27         (((X0) = (k1_xboole_0))
% 12.08/12.27          | ~ (r2_hidden @ X2 @ X1)
% 12.08/12.27          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 12.08/12.27             (k2_zfmisc_1 @ X1 @ X0)))),
% 12.08/12.27      inference('sup-', [status(thm)], ['32', '33'])).
% 12.08/12.27  thf('35', plain,
% 12.08/12.27      (![X0 : $i, X1 : $i]:
% 12.08/12.27         (((X0) = (k1_xboole_0))
% 12.08/12.27          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 12.08/12.27             (k2_zfmisc_1 @ X0 @ X1))
% 12.08/12.27          | ((X1) = (k1_xboole_0)))),
% 12.08/12.27      inference('sup-', [status(thm)], ['31', '34'])).
% 12.08/12.27  thf('36', plain,
% 12.08/12.27      ((((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 12.08/12.27          k1_xboole_0)
% 12.08/12.27         | ((sk_B_1) = (k1_xboole_0))
% 12.08/12.27         | ((sk_A) = (k1_xboole_0))))
% 12.08/12.27         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('sup+', [status(thm)], ['30', '35'])).
% 12.08/12.27  thf('37', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 12.08/12.27      inference('demod', [status(thm)], ['16', '17'])).
% 12.08/12.27  thf('38', plain,
% 12.08/12.27      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 12.08/12.27         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('clc', [status(thm)], ['36', '37'])).
% 12.08/12.27  thf('39', plain,
% 12.08/12.27      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('split', [status(esa)], ['0'])).
% 12.08/12.27  thf('40', plain,
% 12.08/12.27      (((((sk_B_1) != (sk_B_1)) | ((sk_A) = (k1_xboole_0))))
% 12.08/12.27         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 12.08/12.27             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('sup-', [status(thm)], ['38', '39'])).
% 12.08/12.27  thf('41', plain,
% 12.08/12.27      ((((sk_A) = (k1_xboole_0)))
% 12.08/12.27         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 12.08/12.27             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('simplify', [status(thm)], ['40'])).
% 12.08/12.27  thf('42', plain,
% 12.08/12.27      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 12.08/12.27      inference('split', [status(esa)], ['23'])).
% 12.08/12.27  thf('43', plain,
% 12.08/12.27      ((((sk_A) != (sk_A)))
% 12.08/12.27         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 12.08/12.27             ~ (((sk_A) = (k1_xboole_0))) & 
% 12.08/12.27             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 12.08/12.27      inference('sup-', [status(thm)], ['41', '42'])).
% 12.08/12.27  thf('44', plain,
% 12.08/12.27      ((((sk_A) = (k1_xboole_0))) | 
% 12.08/12.27       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 12.08/12.27       (((sk_B_1) = (k1_xboole_0)))),
% 12.08/12.27      inference('simplify', [status(thm)], ['43'])).
% 12.08/12.28  thf('45', plain,
% 12.08/12.28      (![X0 : $i, X1 : $i]:
% 12.08/12.28         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 12.08/12.28          | (zip_tseitin_0 @ 
% 12.08/12.28             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 12.08/12.28             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 12.08/12.28             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 12.08/12.28      inference('sup-', [status(thm)], ['2', '4'])).
% 12.08/12.28  thf('46', plain,
% 12.08/12.28      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 12.08/12.28         ((r2_hidden @ X41 @ X45)
% 12.08/12.28          | ~ (zip_tseitin_0 @ X42 @ X41 @ X43 @ X44 @ X45))),
% 12.08/12.28      inference('cnf', [status(esa)], [zf_stmt_2])).
% 12.08/12.28  thf('47', plain,
% 12.08/12.28      (![X0 : $i, X1 : $i]:
% 12.08/12.28         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 12.08/12.28          | (r2_hidden @ 
% 12.08/12.28             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 12.08/12.28      inference('sup-', [status(thm)], ['45', '46'])).
% 12.08/12.28  thf('48', plain,
% 12.08/12.28      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 12.08/12.28      inference('split', [status(esa)], ['8'])).
% 12.08/12.28  thf('49', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 12.08/12.28      inference('demod', [status(thm)], ['16', '17'])).
% 12.08/12.28  thf('50', plain,
% 12.08/12.28      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 12.08/12.28      inference('sup-', [status(thm)], ['48', '49'])).
% 12.08/12.28  thf('51', plain,
% 12.08/12.28      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0)))
% 12.08/12.28         <= ((((sk_A) = (k1_xboole_0))))),
% 12.08/12.28      inference('sup-', [status(thm)], ['47', '50'])).
% 12.08/12.28  thf('52', plain,
% 12.08/12.28      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 12.08/12.28      inference('split', [status(esa)], ['8'])).
% 12.08/12.28  thf('53', plain,
% 12.08/12.28      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A)))
% 12.08/12.28         <= ((((sk_A) = (k1_xboole_0))))),
% 12.08/12.28      inference('demod', [status(thm)], ['51', '52'])).
% 12.08/12.28  thf('54', plain,
% 12.08/12.28      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 12.08/12.28         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 12.08/12.28      inference('split', [status(esa)], ['23'])).
% 12.08/12.28  thf('55', plain,
% 12.08/12.28      ((((sk_A) != (k1_xboole_0)))
% 12.08/12.28         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 12.08/12.28             (((sk_A) = (k1_xboole_0))))),
% 12.08/12.28      inference('sup-', [status(thm)], ['53', '54'])).
% 12.08/12.28  thf('56', plain,
% 12.08/12.28      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 12.08/12.28      inference('split', [status(esa)], ['8'])).
% 12.08/12.28  thf('57', plain,
% 12.08/12.28      ((((sk_A) != (sk_A)))
% 12.08/12.28         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 12.08/12.28             (((sk_A) = (k1_xboole_0))))),
% 12.08/12.28      inference('demod', [status(thm)], ['55', '56'])).
% 12.08/12.28  thf('58', plain,
% 12.08/12.28      (~ (((sk_A) = (k1_xboole_0))) | 
% 12.08/12.28       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 12.08/12.28      inference('simplify', [status(thm)], ['57'])).
% 12.08/12.28  thf('59', plain,
% 12.08/12.28      ((((sk_A) = (k1_xboole_0))) | 
% 12.08/12.28       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 12.08/12.28       (((sk_B_1) = (k1_xboole_0)))),
% 12.08/12.28      inference('split', [status(esa)], ['8'])).
% 12.08/12.28  thf('60', plain, ($false),
% 12.08/12.28      inference('sat_resolution*', [status(thm)],
% 12.08/12.28                ['1', '28', '29', '44', '58', '59'])).
% 12.08/12.28  
% 12.08/12.28  % SZS output end Refutation
% 12.08/12.28  
% 12.08/12.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
