%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eALh5lEOAM

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:02 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 834 expanded)
%              Number of leaves         :   22 ( 258 expanded)
%              Depth                    :   21
%              Number of atoms          :  843 (7963 expanded)
%              Number of equality atoms :  113 ( 944 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('7',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

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

thf('9',plain,(
    ! [X47: $i,X48: $i,X51: $i] :
      ( ( X51
        = ( k2_zfmisc_1 @ X48 @ X47 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X51 @ X47 @ X48 ) @ ( sk_E @ X51 @ X47 @ X48 ) @ ( sk_D @ X51 @ X47 @ X48 ) @ X47 @ X48 )
      | ( r2_hidden @ ( sk_D @ X51 @ X47 @ X48 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( r2_hidden @ X39 @ X41 )
      | ~ ( zip_tseitin_0 @ X39 @ X38 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('25',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('29',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('39',plain,(
    ! [X56: $i,X57: $i,X58: $i,X60: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X56 @ X58 ) @ ( k2_zfmisc_1 @ X57 @ X60 ) )
      | ~ ( r2_hidden @ X58 @ X60 )
      | ~ ( r2_hidden @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ ( sk_D @ X2 @ k1_xboole_0 @ X3 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','43'])).

thf('45',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('46',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('47',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('49',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','26','27','53'])).

thf('55',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('58',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','26','27','53','57'])).

thf('59',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['56','58'])).

thf('60',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != sk_A ),
    inference(demod,[status(thm)],['55','59'])).

thf('61',plain,(
    ! [X47: $i,X48: $i,X51: $i] :
      ( ( X51
        = ( k2_zfmisc_1 @ X48 @ X47 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X51 @ X47 @ X48 ) @ ( sk_E @ X51 @ X47 @ X48 ) @ ( sk_D @ X51 @ X47 @ X48 ) @ X47 @ X48 )
      | ( r2_hidden @ ( sk_D @ X51 @ X47 @ X48 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( r2_hidden @ X38 @ X42 )
      | ~ ( zip_tseitin_0 @ X39 @ X38 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('66',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('78',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['63','78'])).

thf('80',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('81',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['56','58'])).

thf('83',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['56','58'])).

thf('84',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k2_zfmisc_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['60','84'])).

thf('86',plain,(
    $false ),
    inference(simplify,[status(thm)],['85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eALh5lEOAM
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:25:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.49/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.65  % Solved by: fo/fo7.sh
% 0.49/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.65  % done 271 iterations in 0.192s
% 0.49/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.65  % SZS output start Refutation
% 0.49/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.49/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.49/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.65  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.49/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.49/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.49/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.65  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.49/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.65  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.49/0.65  thf(t113_zfmisc_1, conjecture,
% 0.49/0.65    (![A:$i,B:$i]:
% 0.49/0.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.49/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.49/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.65    (~( ![A:$i,B:$i]:
% 0.49/0.65        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.49/0.65          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.49/0.65    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.49/0.65  thf('0', plain,
% 0.49/0.65      ((((sk_A) != (k1_xboole_0))
% 0.49/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('1', plain,
% 0.49/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.49/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('split', [status(esa)], ['0'])).
% 0.49/0.65  thf('2', plain,
% 0.49/0.65      ((((sk_B) != (k1_xboole_0))
% 0.49/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('3', plain,
% 0.49/0.65      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.49/0.65       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.65      inference('split', [status(esa)], ['2'])).
% 0.49/0.65  thf('4', plain,
% 0.49/0.65      ((((sk_B) = (k1_xboole_0))
% 0.49/0.65        | ((sk_A) = (k1_xboole_0))
% 0.49/0.65        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('5', plain, ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('split', [status(esa)], ['4'])).
% 0.49/0.65  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.49/0.65  thf('6', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.49/0.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.65  thf('7', plain,
% 0.49/0.65      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('sup+', [status(thm)], ['5', '6'])).
% 0.49/0.65  thf('8', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.49/0.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.65  thf(d2_zfmisc_1, axiom,
% 0.49/0.65    (![A:$i,B:$i,C:$i]:
% 0.49/0.65     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.49/0.65       ( ![D:$i]:
% 0.49/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.65           ( ?[E:$i,F:$i]:
% 0.49/0.65             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.49/0.65               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.49/0.65  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.49/0.65  thf(zf_stmt_2, axiom,
% 0.49/0.65    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.49/0.65     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.49/0.65       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.49/0.65         ( r2_hidden @ E @ A ) ) ))).
% 0.49/0.65  thf(zf_stmt_3, axiom,
% 0.49/0.65    (![A:$i,B:$i,C:$i]:
% 0.49/0.65     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.49/0.65       ( ![D:$i]:
% 0.49/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.65           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.49/0.65  thf('9', plain,
% 0.49/0.65      (![X47 : $i, X48 : $i, X51 : $i]:
% 0.49/0.65         (((X51) = (k2_zfmisc_1 @ X48 @ X47))
% 0.49/0.65          | (zip_tseitin_0 @ (sk_F @ X51 @ X47 @ X48) @ 
% 0.49/0.65             (sk_E @ X51 @ X47 @ X48) @ (sk_D @ X51 @ X47 @ X48) @ X47 @ X48)
% 0.49/0.65          | (r2_hidden @ (sk_D @ X51 @ X47 @ X48) @ X51))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.65  thf('10', plain,
% 0.49/0.65      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.49/0.65         ((r2_hidden @ X39 @ X41)
% 0.49/0.65          | ~ (zip_tseitin_0 @ X39 @ X38 @ X40 @ X41 @ X42))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.65  thf('11', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.65         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.49/0.65          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.65          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.49/0.65      inference('sup-', [status(thm)], ['9', '10'])).
% 0.49/0.65  thf(idempotence_k3_xboole_0, axiom,
% 0.49/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.49/0.65  thf('12', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.49/0.65      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.49/0.65  thf(t4_xboole_0, axiom,
% 0.49/0.65    (![A:$i,B:$i]:
% 0.49/0.65     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.49/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.49/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.49/0.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.49/0.65  thf('13', plain,
% 0.49/0.65      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.49/0.65         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.49/0.65          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.49/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.49/0.65  thf('14', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.65  thf('15', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.65         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.49/0.65          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.65          | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['11', '14'])).
% 0.49/0.65  thf('16', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 0.49/0.65          | (r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['8', '15'])).
% 0.49/0.65  thf('17', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.65  thf('18', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.65  thf('19', plain,
% 0.49/0.65      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.49/0.65         <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('sup-', [status(thm)], ['7', '18'])).
% 0.49/0.65  thf('20', plain,
% 0.49/0.65      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('split', [status(esa)], ['4'])).
% 0.49/0.65  thf('21', plain,
% 0.49/0.65      ((![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.49/0.65         <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('demod', [status(thm)], ['19', '20'])).
% 0.49/0.65  thf('22', plain,
% 0.49/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.49/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('split', [status(esa)], ['0'])).
% 0.49/0.65  thf('23', plain,
% 0.49/0.65      ((((sk_B) != (k1_xboole_0)))
% 0.49/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.49/0.65             (((sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('sup-', [status(thm)], ['21', '22'])).
% 0.49/0.65  thf('24', plain,
% 0.49/0.65      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('split', [status(esa)], ['4'])).
% 0.49/0.65  thf('25', plain,
% 0.49/0.65      ((((sk_B) != (sk_B)))
% 0.49/0.65         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.49/0.65             (((sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.49/0.65  thf('26', plain,
% 0.49/0.65      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.49/0.65       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.65      inference('simplify', [status(thm)], ['25'])).
% 0.49/0.65  thf('27', plain,
% 0.49/0.65      (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.49/0.65       ~ (((sk_A) = (k1_xboole_0)))),
% 0.49/0.65      inference('split', [status(esa)], ['0'])).
% 0.49/0.65  thf('28', plain,
% 0.49/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.49/0.65         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('split', [status(esa)], ['4'])).
% 0.49/0.65  thf('29', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.49/0.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.65  thf('30', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.65         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.49/0.65          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.65          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.49/0.65      inference('sup-', [status(thm)], ['9', '10'])).
% 0.49/0.65  thf('31', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.65  thf('32', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.65         (((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 0.49/0.65          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X2)
% 0.49/0.65          | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.49/0.65  thf('33', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ X0)
% 0.49/0.65          | ((X0) = (k2_zfmisc_1 @ X1 @ k1_xboole_0)))),
% 0.49/0.65      inference('sup-', [status(thm)], ['29', '32'])).
% 0.49/0.65  thf('34', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.49/0.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.65  thf('35', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.65  thf('36', plain,
% 0.49/0.65      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.49/0.65  thf('37', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ X0)
% 0.49/0.65          | ((X0) = (k1_xboole_0)))),
% 0.49/0.65      inference('demod', [status(thm)], ['33', '36'])).
% 0.49/0.65  thf('38', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ X0)
% 0.49/0.65          | ((X0) = (k1_xboole_0)))),
% 0.49/0.65      inference('demod', [status(thm)], ['33', '36'])).
% 0.49/0.65  thf(l54_zfmisc_1, axiom,
% 0.49/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.65     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.49/0.65       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.49/0.65  thf('39', plain,
% 0.49/0.65      (![X56 : $i, X57 : $i, X58 : $i, X60 : $i]:
% 0.49/0.65         ((r2_hidden @ (k4_tarski @ X56 @ X58) @ (k2_zfmisc_1 @ X57 @ X60))
% 0.49/0.65          | ~ (r2_hidden @ X58 @ X60)
% 0.49/0.65          | ~ (r2_hidden @ X56 @ X57))),
% 0.49/0.65      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.49/0.65  thf('40', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.65         (((X0) = (k1_xboole_0))
% 0.49/0.65          | ~ (r2_hidden @ X3 @ X2)
% 0.49/0.65          | (r2_hidden @ (k4_tarski @ X3 @ (sk_D @ X0 @ k1_xboole_0 @ X1)) @ 
% 0.49/0.65             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.49/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.49/0.65  thf('41', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.65         (((X0) = (k1_xboole_0))
% 0.49/0.65          | (r2_hidden @ 
% 0.49/0.65             (k4_tarski @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ 
% 0.49/0.65              (sk_D @ X2 @ k1_xboole_0 @ X3)) @ 
% 0.49/0.65             (k2_zfmisc_1 @ X0 @ X2))
% 0.49/0.65          | ((X2) = (k1_xboole_0)))),
% 0.49/0.65      inference('sup-', [status(thm)], ['37', '40'])).
% 0.49/0.65  thf('42', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.65  thf('43', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (((X0) = (k1_xboole_0))
% 0.49/0.65          | ((X1) = (k1_xboole_0))
% 0.49/0.65          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.49/0.65      inference('sup-', [status(thm)], ['41', '42'])).
% 0.49/0.65  thf('44', plain,
% 0.49/0.65      (((~ (r1_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.49/0.65         | ((sk_A) = (k1_xboole_0))
% 0.49/0.65         | ((sk_B) = (k1_xboole_0))))
% 0.49/0.65         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('sup-', [status(thm)], ['28', '43'])).
% 0.49/0.65  thf('45', plain,
% 0.49/0.65      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.49/0.65         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('split', [status(esa)], ['4'])).
% 0.49/0.65  thf('46', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.49/0.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.65  thf('47', plain,
% 0.49/0.65      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.49/0.65         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.49/0.65  thf('48', plain,
% 0.49/0.65      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('split', [status(esa)], ['2'])).
% 0.49/0.65  thf('49', plain,
% 0.49/0.65      (((((sk_B) != (sk_B)) | ((sk_A) = (k1_xboole_0))))
% 0.49/0.65         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.49/0.65             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('sup-', [status(thm)], ['47', '48'])).
% 0.49/0.65  thf('50', plain,
% 0.49/0.65      ((((sk_A) = (k1_xboole_0)))
% 0.49/0.65         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.49/0.65             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('simplify', [status(thm)], ['49'])).
% 0.49/0.65  thf('51', plain,
% 0.49/0.65      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.49/0.65      inference('split', [status(esa)], ['0'])).
% 0.49/0.65  thf('52', plain,
% 0.49/0.65      ((((sk_A) != (sk_A)))
% 0.49/0.65         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.49/0.65             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.49/0.65             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.65      inference('sup-', [status(thm)], ['50', '51'])).
% 0.49/0.65  thf('53', plain,
% 0.49/0.65      ((((sk_A) = (k1_xboole_0))) | 
% 0.49/0.65       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.49/0.65       (((sk_B) = (k1_xboole_0)))),
% 0.49/0.65      inference('simplify', [status(thm)], ['52'])).
% 0.49/0.65  thf('54', plain, (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.65      inference('sat_resolution*', [status(thm)], ['3', '26', '27', '53'])).
% 0.49/0.65  thf('55', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.49/0.65      inference('simpl_trail', [status(thm)], ['1', '54'])).
% 0.49/0.65  thf('56', plain,
% 0.49/0.65      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.65      inference('split', [status(esa)], ['4'])).
% 0.49/0.65  thf('57', plain,
% 0.49/0.65      ((((sk_A) = (k1_xboole_0))) | 
% 0.49/0.65       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.49/0.65       (((sk_B) = (k1_xboole_0)))),
% 0.49/0.65      inference('split', [status(esa)], ['4'])).
% 0.49/0.65  thf('58', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.49/0.65      inference('sat_resolution*', [status(thm)], ['3', '26', '27', '53', '57'])).
% 0.49/0.65  thf('59', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.65      inference('simpl_trail', [status(thm)], ['56', '58'])).
% 0.49/0.65  thf('60', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (sk_A))),
% 0.49/0.65      inference('demod', [status(thm)], ['55', '59'])).
% 0.49/0.65  thf('61', plain,
% 0.49/0.65      (![X47 : $i, X48 : $i, X51 : $i]:
% 0.49/0.65         (((X51) = (k2_zfmisc_1 @ X48 @ X47))
% 0.49/0.65          | (zip_tseitin_0 @ (sk_F @ X51 @ X47 @ X48) @ 
% 0.49/0.65             (sk_E @ X51 @ X47 @ X48) @ (sk_D @ X51 @ X47 @ X48) @ X47 @ X48)
% 0.49/0.65          | (r2_hidden @ (sk_D @ X51 @ X47 @ X48) @ X51))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.65  thf('62', plain,
% 0.49/0.65      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.49/0.65         ((r2_hidden @ X38 @ X42)
% 0.49/0.65          | ~ (zip_tseitin_0 @ X39 @ X38 @ X40 @ X41 @ X42))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.66  thf('63', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.66         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.49/0.66          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.66          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.49/0.66      inference('sup-', [status(thm)], ['61', '62'])).
% 0.49/0.66  thf('64', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.49/0.66      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.66  thf('65', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.49/0.66      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.49/0.66  thf('66', plain,
% 0.49/0.66      (![X1 : $i, X2 : $i]:
% 0.49/0.66         ((r1_xboole_0 @ X1 @ X2)
% 0.49/0.66          | (r2_hidden @ (sk_C @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X2)))),
% 0.49/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.49/0.66  thf('67', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         ((r2_hidden @ (sk_C @ X0 @ X0) @ X0) | (r1_xboole_0 @ X0 @ X0))),
% 0.49/0.66      inference('sup+', [status(thm)], ['65', '66'])).
% 0.49/0.66  thf('68', plain,
% 0.49/0.66      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.49/0.66         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.49/0.66          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.49/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.49/0.66  thf('69', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.49/0.66          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.49/0.66      inference('sup-', [status(thm)], ['67', '68'])).
% 0.49/0.66  thf('70', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.49/0.66          (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.66      inference('sup-', [status(thm)], ['64', '69'])).
% 0.49/0.66  thf('71', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ X0)
% 0.49/0.66          | ((X0) = (k1_xboole_0)))),
% 0.49/0.66      inference('demod', [status(thm)], ['33', '36'])).
% 0.49/0.66  thf('72', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.49/0.66      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.66  thf('73', plain,
% 0.49/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.49/0.66      inference('sup-', [status(thm)], ['71', '72'])).
% 0.49/0.66  thf('74', plain,
% 0.49/0.66      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.66      inference('sup-', [status(thm)], ['70', '73'])).
% 0.49/0.66  thf('75', plain,
% 0.49/0.66      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.49/0.66         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.49/0.66          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.49/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.49/0.66  thf('76', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.66      inference('sup-', [status(thm)], ['74', '75'])).
% 0.49/0.66  thf('77', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.49/0.66      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.66  thf('78', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.49/0.66      inference('demod', [status(thm)], ['76', '77'])).
% 0.49/0.66  thf('79', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.49/0.66          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.49/0.66      inference('sup-', [status(thm)], ['63', '78'])).
% 0.49/0.66  thf('80', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.49/0.66      inference('demod', [status(thm)], ['76', '77'])).
% 0.49/0.66  thf('81', plain,
% 0.49/0.66      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.49/0.66      inference('sup-', [status(thm)], ['79', '80'])).
% 0.49/0.66  thf('82', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.66      inference('simpl_trail', [status(thm)], ['56', '58'])).
% 0.49/0.66  thf('83', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.66      inference('simpl_trail', [status(thm)], ['56', '58'])).
% 0.49/0.66  thf('84', plain, (![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0))),
% 0.49/0.66      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.49/0.66  thf('85', plain, (((sk_A) != (sk_A))),
% 0.49/0.66      inference('demod', [status(thm)], ['60', '84'])).
% 0.49/0.66  thf('86', plain, ($false), inference('simplify', [status(thm)], ['85'])).
% 0.49/0.66  
% 0.49/0.66  % SZS output end Refutation
% 0.49/0.66  
% 0.49/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
