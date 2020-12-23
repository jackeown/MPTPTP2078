%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5XhlsS2iPm

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:00 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 151 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  725 (1192 expanded)
%              Number of equality atoms :   95 ( 171 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ( sk_B_2 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('5',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_2 @ X0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','8'])).

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

thf('10',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ( X21
        = ( k2_zfmisc_1 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X21 @ X17 @ X18 ) @ ( sk_E @ X21 @ X17 @ X18 ) @ ( sk_D @ X21 @ X17 @ X18 ) @ X17 @ X18 )
      | ( r2_hidden @ ( sk_D @ X21 @ X17 @ X18 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ X11 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ sk_B_2 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('26',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('29',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X13 )
      | ~ ( r2_hidden @ X8 @ X13 )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ( X10
       != ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,(
    ! [X8: $i,X9: $i,X11: $i,X13: $i] :
      ( ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X8 @ X13 )
      | ( zip_tseitin_0 @ X9 @ X8 @ ( k4_tarski @ X8 @ X9 ) @ X11 @ X13 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B_1 @ X0 ) @ X2 @ ( k4_tarski @ X2 @ ( sk_B_1 @ X0 ) ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B_1 @ X1 ) @ ( sk_B_1 @ X0 ) @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( sk_B_1 @ X1 ) ) @ X1 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X16 @ X19 )
      | ( X19
       != ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X18 @ X17 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( sk_B_1 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_B_1 @ sk_B_2 ) ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,
    ( ( ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('41',plain,
    ( ( ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('46',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('49',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_A @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ( X21
        = ( k2_zfmisc_1 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X21 @ X17 @ X18 ) @ ( sk_E @ X21 @ X17 @ X18 ) @ ( sk_D @ X21 @ X17 @ X18 ) @ X17 @ X18 )
      | ( r2_hidden @ ( sk_D @ X21 @ X17 @ X18 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X8 @ X12 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ sk_A )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('64',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','64'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('67',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','25','26','47','65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5XhlsS2iPm
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:52:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 362 iterations in 0.210s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.45/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.67  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.67  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.45/0.67  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.45/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(t113_zfmisc_1, conjecture,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.67       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i]:
% 0.45/0.67        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.67          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      ((((sk_B_2) != (k1_xboole_0))
% 0.45/0.67        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) != (k1_xboole_0)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      (~ (((sk_B_2) = (k1_xboole_0))) | 
% 0.45/0.67       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.45/0.67      inference('split', [status(esa)], ['0'])).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      ((((sk_B_2) = (k1_xboole_0))
% 0.45/0.67        | ((sk_A) = (k1_xboole_0))
% 0.45/0.67        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('split', [status(esa)], ['2'])).
% 0.45/0.67  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.67  thf('4', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      ((![X0 : $i]: (r1_tarski @ sk_B_2 @ X0))
% 0.45/0.67         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['3', '4'])).
% 0.45/0.67  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.45/0.67  thf('6', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.45/0.67      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.45/0.67  thf(t69_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.67       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (r1_xboole_0 @ X6 @ X7)
% 0.45/0.67          | ~ (r1_tarski @ X6 @ X7)
% 0.45/0.67          | (v1_xboole_0 @ X6))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.67  thf('9', plain, (((v1_xboole_0 @ sk_B_2)) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['5', '8'])).
% 0.45/0.67  thf(d2_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.45/0.67       ( ![D:$i]:
% 0.45/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.67           ( ?[E:$i,F:$i]:
% 0.45/0.67             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.45/0.67               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.45/0.67  thf(zf_stmt_2, axiom,
% 0.45/0.67    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.45/0.67     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.45/0.67       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.45/0.67         ( r2_hidden @ E @ A ) ) ))).
% 0.45/0.67  thf(zf_stmt_3, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.45/0.67       ( ![D:$i]:
% 0.45/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.67           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X17 : $i, X18 : $i, X21 : $i]:
% 0.45/0.67         (((X21) = (k2_zfmisc_1 @ X18 @ X17))
% 0.45/0.67          | (zip_tseitin_0 @ (sk_F @ X21 @ X17 @ X18) @ 
% 0.45/0.67             (sk_E @ X21 @ X17 @ X18) @ (sk_D @ X21 @ X17 @ X18) @ X17 @ X18)
% 0.45/0.67          | (r2_hidden @ (sk_D @ X21 @ X17 @ X18) @ X21))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.67         ((r2_hidden @ X9 @ X11)
% 0.45/0.67          | ~ (zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.45/0.67          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.45/0.67          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.67  thf(d1_xboole_0, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.45/0.67          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.45/0.67          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (~ (v1_xboole_0 @ X2)
% 0.45/0.67          | ((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 0.45/0.67          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      ((((sk_A) != (k1_xboole_0))
% 0.45/0.67        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) != (k1_xboole_0)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) != (k1_xboole_0)))
% 0.45/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('split', [status(esa)], ['17'])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          (((X0) != (k1_xboole_0))
% 0.45/0.67           | ~ (v1_xboole_0 @ sk_B_2)
% 0.45/0.67           | ~ (v1_xboole_0 @ X0)))
% 0.45/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['16', '18'])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_2)))
% 0.45/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.67  thf('21', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.67  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      ((~ (v1_xboole_0 @ sk_B_2))
% 0.45/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('simplify_reflect+', [status(thm)], ['20', '23'])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (~ (((sk_B_2) = (k1_xboole_0))) | 
% 0.45/0.67       (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['9', '24'])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.45/0.67       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.45/0.67      inference('split', [status(esa)], ['17'])).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))
% 0.45/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('split', [status(esa)], ['2'])).
% 0.45/0.67  thf(t7_xboole_0, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.67          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.45/0.67         ((zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X13)
% 0.45/0.67          | ~ (r2_hidden @ X8 @ X13)
% 0.45/0.67          | ~ (r2_hidden @ X9 @ X11)
% 0.45/0.67          | ((X10) != (k4_tarski @ X8 @ X9)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      (![X8 : $i, X9 : $i, X11 : $i, X13 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X9 @ X11)
% 0.45/0.67          | ~ (r2_hidden @ X8 @ X13)
% 0.45/0.67          | (zip_tseitin_0 @ X9 @ X8 @ (k4_tarski @ X8 @ X9) @ X11 @ X13))),
% 0.45/0.67      inference('simplify', [status(thm)], ['30'])).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (((X0) = (k1_xboole_0))
% 0.45/0.67          | (zip_tseitin_0 @ (sk_B_1 @ X0) @ X2 @ 
% 0.45/0.67             (k4_tarski @ X2 @ (sk_B_1 @ X0)) @ X0 @ X1)
% 0.45/0.67          | ~ (r2_hidden @ X2 @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['29', '31'])).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((X0) = (k1_xboole_0))
% 0.45/0.67          | (zip_tseitin_0 @ (sk_B_1 @ X1) @ (sk_B_1 @ X0) @ 
% 0.45/0.67             (k4_tarski @ (sk_B_1 @ X0) @ (sk_B_1 @ X1)) @ X1 @ X0)
% 0.45/0.67          | ((X1) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['28', '32'])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.67         (~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.45/0.67          | (r2_hidden @ X16 @ X19)
% 0.45/0.67          | ((X19) != (k2_zfmisc_1 @ X18 @ X17)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.67         ((r2_hidden @ X16 @ (k2_zfmisc_1 @ X18 @ X17))
% 0.45/0.67          | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.45/0.67      inference('simplify', [status(thm)], ['34'])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((X1) = (k1_xboole_0))
% 0.45/0.67          | ((X0) = (k1_xboole_0))
% 0.45/0.67          | (r2_hidden @ (k4_tarski @ (sk_B_1 @ X0) @ (sk_B_1 @ X1)) @ 
% 0.45/0.67             (k2_zfmisc_1 @ X0 @ X1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['33', '35'])).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      ((((r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_A) @ (sk_B_1 @ sk_B_2)) @ 
% 0.45/0.67          k1_xboole_0)
% 0.45/0.67         | ((sk_A) = (k1_xboole_0))
% 0.45/0.67         | ((sk_B_2) = (k1_xboole_0))))
% 0.45/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['27', '36'])).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      (((((sk_B_2) = (k1_xboole_0))
% 0.45/0.67         | ((sk_A) = (k1_xboole_0))
% 0.45/0.67         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.45/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.67  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.67  thf('41', plain,
% 0.45/0.67      (((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.45/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('demod', [status(thm)], ['39', '40'])).
% 0.45/0.67  thf('42', plain,
% 0.45/0.67      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('split', [status(esa)], ['0'])).
% 0.45/0.67  thf('43', plain,
% 0.45/0.67      (((((sk_B_2) != (sk_B_2)) | ((sk_A) = (k1_xboole_0))))
% 0.45/0.67         <= (~ (((sk_B_2) = (k1_xboole_0))) & 
% 0.45/0.67             (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.67  thf('44', plain,
% 0.45/0.67      ((((sk_A) = (k1_xboole_0)))
% 0.45/0.67         <= (~ (((sk_B_2) = (k1_xboole_0))) & 
% 0.45/0.67             (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('simplify', [status(thm)], ['43'])).
% 0.45/0.67  thf('45', plain,
% 0.45/0.67      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.45/0.67      inference('split', [status(esa)], ['17'])).
% 0.45/0.67  thf('46', plain,
% 0.45/0.67      ((((sk_A) != (sk_A)))
% 0.45/0.67         <= (~ (((sk_B_2) = (k1_xboole_0))) & 
% 0.45/0.67             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.45/0.67             (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.67  thf('47', plain,
% 0.45/0.67      ((((sk_A) = (k1_xboole_0))) | 
% 0.45/0.67       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))) | 
% 0.45/0.67       (((sk_B_2) = (k1_xboole_0)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.67  thf('48', plain,
% 0.45/0.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.67      inference('split', [status(esa)], ['2'])).
% 0.45/0.67  thf('49', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.67  thf('50', plain,
% 0.45/0.67      ((![X0 : $i]: (r1_tarski @ sk_A @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['48', '49'])).
% 0.45/0.67  thf('51', plain,
% 0.45/0.67      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.67  thf('52', plain, (((v1_xboole_0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.67  thf('53', plain,
% 0.45/0.67      (![X17 : $i, X18 : $i, X21 : $i]:
% 0.45/0.67         (((X21) = (k2_zfmisc_1 @ X18 @ X17))
% 0.45/0.67          | (zip_tseitin_0 @ (sk_F @ X21 @ X17 @ X18) @ 
% 0.45/0.67             (sk_E @ X21 @ X17 @ X18) @ (sk_D @ X21 @ X17 @ X18) @ X17 @ X18)
% 0.45/0.67          | (r2_hidden @ (sk_D @ X21 @ X17 @ X18) @ X21))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.67  thf('54', plain,
% 0.45/0.67      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.67         ((r2_hidden @ X8 @ X12)
% 0.45/0.67          | ~ (zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.67  thf('55', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.45/0.67          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.45/0.67          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.67  thf('56', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.67  thf('57', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 0.45/0.67          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.45/0.67          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.67  thf('58', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.67  thf('59', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (~ (v1_xboole_0 @ X2)
% 0.45/0.67          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.45/0.67          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.67  thf('60', plain,
% 0.45/0.67      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) != (k1_xboole_0)))
% 0.45/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('split', [status(esa)], ['17'])).
% 0.45/0.67  thf('61', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          (((X0) != (k1_xboole_0))
% 0.45/0.67           | ~ (v1_xboole_0 @ sk_A)
% 0.45/0.67           | ~ (v1_xboole_0 @ X0)))
% 0.45/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['59', '60'])).
% 0.45/0.67  thf('62', plain,
% 0.45/0.67      (((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_A)))
% 0.45/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('simplify', [status(thm)], ['61'])).
% 0.45/0.67  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.67  thf('64', plain,
% 0.45/0.67      ((~ (v1_xboole_0 @ sk_A))
% 0.45/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.45/0.67      inference('simplify_reflect+', [status(thm)], ['62', '63'])).
% 0.45/0.67  thf('65', plain,
% 0.45/0.67      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.45/0.67       (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['52', '64'])).
% 0.45/0.67  thf('66', plain,
% 0.45/0.67      ((((sk_A) = (k1_xboole_0))) | 
% 0.45/0.67       (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))) | 
% 0.45/0.67       (((sk_B_2) = (k1_xboole_0)))),
% 0.45/0.67      inference('split', [status(esa)], ['2'])).
% 0.45/0.67  thf('67', plain, ($false),
% 0.45/0.67      inference('sat_resolution*', [status(thm)],
% 0.45/0.67                ['1', '25', '26', '47', '65', '66'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
