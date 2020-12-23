%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KYEPCKoLgd

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:01 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  138 (2023 expanded)
%              Number of leaves         :   28 ( 662 expanded)
%              Depth                    :   28
%              Number of atoms          : 1084 (15754 expanded)
%              Number of equality atoms :  132 (1837 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

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

thf('4',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ( X21
        = ( k2_zfmisc_1 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X21 @ X17 @ X18 ) @ ( sk_E @ X21 @ X17 @ X18 ) @ ( sk_D @ X21 @ X17 @ X18 ) @ X17 @ X18 )
      | ( r2_hidden @ ( sk_D @ X21 @ X17 @ X18 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ X11 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('18',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X29: $i] :
      ( ( X29
        = ( k3_tarski @ X25 ) )
      | ( r2_hidden @ ( sk_D_1 @ X29 @ X25 ) @ X25 )
      | ( r2_hidden @ ( sk_C_1 @ X29 @ X25 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('26',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k4_xboole_0 @ X0 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','31'])).

thf('33',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ X0 @ X0 ) )
       != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ X0 @ X0 ) )
       != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_xboole_0 != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','36'])).

thf('38',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('39',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('53',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('54',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('58',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X13 )
      | ~ ( r2_hidden @ X8 @ X13 )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ( X10
       != ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('59',plain,(
    ! [X8: $i,X9: $i,X11: $i,X13: $i] :
      ( ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X8 @ X13 )
      | ( zip_tseitin_0 @ X9 @ X8 @ ( k4_tarski @ X8 @ X9 ) @ X11 @ X13 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ X1 ) @ X3 @ ( k4_tarski @ X3 @ ( sk_C @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X2 @ X3 ) @ ( sk_C @ X0 @ X1 ) @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_C @ X2 @ X3 ) ) @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X16 @ X19 )
      | ( X19
       != ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('63',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X18 @ X17 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X3 @ X2 )
      | ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_C @ X2 @ X3 ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X0 ) @ ( sk_C @ X1 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) )
      | ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('67',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X2 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) ) )
      | ( r1_xboole_0 @ X1 @ X1 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X1 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ sk_B @ sk_B )
      | ( r1_xboole_0 @ sk_A @ sk_A ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','72'])).

thf('74',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('75',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('76',plain,
    ( ( ( r1_xboole_0 @ sk_B @ sk_B )
      | ( r1_xboole_0 @ sk_A @ sk_A ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( r1_xboole_0 @ sk_A @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('82',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('84',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','40','41','88'])).

thf('90',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','89'])).

thf('91',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('92',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('93',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','40','41','88','92'])).

thf('94',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['91','93'])).

thf('95',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != sk_A ),
    inference(demod,[status(thm)],['90','94'])).

thf('96',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ( X21
        = ( k2_zfmisc_1 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X21 @ X17 @ X18 ) @ ( sk_E @ X21 @ X17 @ X18 ) @ ( sk_D @ X21 @ X17 @ X18 ) @ X17 @ X18 )
      | ( r2_hidden @ ( sk_D @ X21 @ X17 @ X18 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('97',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X8 @ X12 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('100',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('101',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','40','41','88','92'])).

thf('103',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ sk_A @ X1 @ X0 ) @ X0 )
      | ( sk_A
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['101','102'])).

thf('106',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k2_zfmisc_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['95','106'])).

thf('108',plain,(
    $false ),
    inference(simplify,[status(thm)],['107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KYEPCKoLgd
% 0.13/0.37  % Computer   : n018.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 09:32:57 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.81/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.81/1.03  % Solved by: fo/fo7.sh
% 0.81/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.03  % done 1235 iterations in 0.578s
% 0.81/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.81/1.03  % SZS output start Refutation
% 0.81/1.03  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.81/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.81/1.03  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.81/1.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.81/1.03  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.81/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.81/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.81/1.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.81/1.03  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.81/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.81/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.03  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.81/1.03  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.81/1.03  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.81/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.81/1.03  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.81/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.81/1.03  thf(t113_zfmisc_1, conjecture,
% 0.81/1.03    (![A:$i,B:$i]:
% 0.81/1.03     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.81/1.03       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.81/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.81/1.03    (~( ![A:$i,B:$i]:
% 0.81/1.03        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.81/1.03          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.81/1.03    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.81/1.03  thf('0', plain,
% 0.81/1.03      ((((sk_A) != (k1_xboole_0))
% 0.81/1.03        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('1', plain,
% 0.81/1.03      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.81/1.03         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('split', [status(esa)], ['0'])).
% 0.81/1.03  thf('2', plain,
% 0.81/1.03      ((((sk_B) != (k1_xboole_0))
% 0.81/1.03        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('3', plain,
% 0.81/1.03      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.81/1.03       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.81/1.03      inference('split', [status(esa)], ['2'])).
% 0.81/1.03  thf(d2_zfmisc_1, axiom,
% 0.81/1.03    (![A:$i,B:$i,C:$i]:
% 0.81/1.03     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.81/1.03       ( ![D:$i]:
% 0.81/1.03         ( ( r2_hidden @ D @ C ) <=>
% 0.81/1.03           ( ?[E:$i,F:$i]:
% 0.81/1.03             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.81/1.03               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.81/1.03  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.81/1.03  thf(zf_stmt_2, axiom,
% 0.81/1.03    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.81/1.03     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.81/1.03       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.81/1.03         ( r2_hidden @ E @ A ) ) ))).
% 0.81/1.03  thf(zf_stmt_3, axiom,
% 0.81/1.03    (![A:$i,B:$i,C:$i]:
% 0.81/1.03     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.81/1.03       ( ![D:$i]:
% 0.81/1.03         ( ( r2_hidden @ D @ C ) <=>
% 0.81/1.03           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.81/1.03  thf('4', plain,
% 0.81/1.03      (![X17 : $i, X18 : $i, X21 : $i]:
% 0.81/1.03         (((X21) = (k2_zfmisc_1 @ X18 @ X17))
% 0.81/1.03          | (zip_tseitin_0 @ (sk_F @ X21 @ X17 @ X18) @ 
% 0.81/1.03             (sk_E @ X21 @ X17 @ X18) @ (sk_D @ X21 @ X17 @ X18) @ X17 @ X18)
% 0.81/1.03          | (r2_hidden @ (sk_D @ X21 @ X17 @ X18) @ X21))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.81/1.03  thf('5', plain,
% 0.81/1.03      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.81/1.03         ((r2_hidden @ X9 @ X11)
% 0.81/1.03          | ~ (zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.81/1.03  thf('6', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.03         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.81/1.03          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.81/1.03          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.81/1.03      inference('sup-', [status(thm)], ['4', '5'])).
% 0.81/1.03  thf(t3_boole, axiom,
% 0.81/1.03    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.81/1.03  thf('7', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.81/1.03      inference('cnf', [status(esa)], [t3_boole])).
% 0.81/1.03  thf(t48_xboole_1, axiom,
% 0.81/1.03    (![A:$i,B:$i]:
% 0.81/1.03     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.81/1.03  thf('8', plain,
% 0.81/1.03      (![X5 : $i, X6 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.81/1.03           = (k3_xboole_0 @ X5 @ X6))),
% 0.81/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/1.03  thf('9', plain,
% 0.81/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.03      inference('sup+', [status(thm)], ['7', '8'])).
% 0.81/1.03  thf('10', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.81/1.03      inference('cnf', [status(esa)], [t3_boole])).
% 0.81/1.03  thf('11', plain,
% 0.81/1.03      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/1.03      inference('sup+', [status(thm)], ['9', '10'])).
% 0.81/1.03  thf(t4_xboole_0, axiom,
% 0.81/1.03    (![A:$i,B:$i]:
% 0.81/1.03     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.81/1.03            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.81/1.03       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.81/1.03            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.81/1.03  thf('12', plain,
% 0.81/1.03      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.81/1.03          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.81/1.03      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.81/1.03  thf('13', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.81/1.03          | ~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['11', '12'])).
% 0.81/1.03  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.81/1.03  thf('14', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.81/1.03      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.81/1.03  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.81/1.03      inference('demod', [status(thm)], ['13', '14'])).
% 0.81/1.03  thf('16', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.81/1.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['6', '15'])).
% 0.81/1.03  thf('17', plain,
% 0.81/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.03      inference('sup+', [status(thm)], ['7', '8'])).
% 0.81/1.03  thf('18', plain,
% 0.81/1.03      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.81/1.03          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.81/1.03      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.81/1.03  thf('19', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.81/1.03          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['17', '18'])).
% 0.81/1.03  thf('20', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.81/1.03      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.81/1.03  thf('21', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('demod', [status(thm)], ['19', '20'])).
% 0.81/1.03  thf('22', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['16', '21'])).
% 0.81/1.03  thf(d4_tarski, axiom,
% 0.81/1.03    (![A:$i,B:$i]:
% 0.81/1.03     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.81/1.03       ( ![C:$i]:
% 0.81/1.03         ( ( r2_hidden @ C @ B ) <=>
% 0.81/1.03           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.81/1.03  thf('23', plain,
% 0.81/1.03      (![X25 : $i, X29 : $i]:
% 0.81/1.03         (((X29) = (k3_tarski @ X25))
% 0.81/1.03          | (r2_hidden @ (sk_D_1 @ X29 @ X25) @ X25)
% 0.81/1.03          | (r2_hidden @ (sk_C_1 @ X29 @ X25) @ X29))),
% 0.81/1.03      inference('cnf', [status(esa)], [d4_tarski])).
% 0.81/1.03  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.81/1.03      inference('demod', [status(thm)], ['13', '14'])).
% 0.81/1.03  thf('25', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.81/1.03          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['23', '24'])).
% 0.81/1.03  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.81/1.03  thf('26', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/1.03      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.81/1.03  thf('27', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.81/1.03          | ((X0) = (k1_xboole_0)))),
% 0.81/1.03      inference('demod', [status(thm)], ['25', '26'])).
% 0.81/1.03  thf('28', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('demod', [status(thm)], ['19', '20'])).
% 0.81/1.03  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['27', '28'])).
% 0.81/1.03  thf('30', plain,
% 0.81/1.03      ((((sk_B) = (k1_xboole_0))
% 0.81/1.03        | ((sk_A) = (k1_xboole_0))
% 0.81/1.03        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('31', plain,
% 0.81/1.03      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('split', [status(esa)], ['30'])).
% 0.81/1.03  thf('32', plain,
% 0.81/1.03      ((![X0 : $i]: ((sk_B) = (k4_xboole_0 @ X0 @ X0)))
% 0.81/1.03         <= ((((sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('sup+', [status(thm)], ['29', '31'])).
% 0.81/1.03  thf('33', plain,
% 0.81/1.03      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.81/1.03         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('split', [status(esa)], ['0'])).
% 0.81/1.03  thf('34', plain,
% 0.81/1.03      ((![X0 : $i]:
% 0.81/1.03          ((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ X0 @ X0)) != (k1_xboole_0)))
% 0.81/1.03         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.81/1.03             (((sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['32', '33'])).
% 0.81/1.03  thf('35', plain,
% 0.81/1.03      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('split', [status(esa)], ['30'])).
% 0.81/1.03  thf('36', plain,
% 0.81/1.03      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ X0 @ X0)) != (sk_B)))
% 0.81/1.03         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.81/1.03             (((sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('demod', [status(thm)], ['34', '35'])).
% 0.81/1.03  thf('37', plain,
% 0.81/1.03      ((((k1_xboole_0) != (sk_B)))
% 0.81/1.03         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.81/1.03             (((sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['22', '36'])).
% 0.81/1.03  thf('38', plain,
% 0.81/1.03      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('split', [status(esa)], ['30'])).
% 0.81/1.03  thf('39', plain,
% 0.81/1.03      ((((sk_B) != (sk_B)))
% 0.81/1.03         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.81/1.03             (((sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('demod', [status(thm)], ['37', '38'])).
% 0.81/1.03  thf('40', plain,
% 0.81/1.03      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.81/1.03       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.81/1.03      inference('simplify', [status(thm)], ['39'])).
% 0.81/1.03  thf('41', plain,
% 0.81/1.03      (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.81/1.03       ~ (((sk_A) = (k1_xboole_0)))),
% 0.81/1.03      inference('split', [status(esa)], ['0'])).
% 0.81/1.03  thf('42', plain,
% 0.81/1.03      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.81/1.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('split', [status(esa)], ['30'])).
% 0.81/1.03  thf('43', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.81/1.03          | ((X0) = (k1_xboole_0)))),
% 0.81/1.03      inference('demod', [status(thm)], ['25', '26'])).
% 0.81/1.03  thf('44', plain,
% 0.81/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.03      inference('sup+', [status(thm)], ['7', '8'])).
% 0.81/1.03  thf('45', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('demod', [status(thm)], ['19', '20'])).
% 0.81/1.03  thf('46', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['44', '45'])).
% 0.81/1.03  thf('47', plain,
% 0.81/1.03      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['43', '46'])).
% 0.81/1.03  thf('48', plain,
% 0.81/1.03      (![X5 : $i, X6 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.81/1.03           = (k3_xboole_0 @ X5 @ X6))),
% 0.81/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/1.03  thf('49', plain,
% 0.81/1.03      (![X5 : $i, X6 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.81/1.03           = (k3_xboole_0 @ X5 @ X6))),
% 0.81/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/1.03  thf('50', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.81/1.03           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.81/1.03      inference('sup+', [status(thm)], ['48', '49'])).
% 0.81/1.03  thf('51', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.81/1.03           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.81/1.03      inference('sup+', [status(thm)], ['47', '50'])).
% 0.81/1.03  thf('52', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.81/1.03      inference('cnf', [status(esa)], [t3_boole])).
% 0.81/1.03  thf('53', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.81/1.03      inference('cnf', [status(esa)], [t3_boole])).
% 0.81/1.03  thf('54', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.81/1.03  thf('55', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.81/1.03  thf('56', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         ((r1_xboole_0 @ X0 @ X1)
% 0.81/1.03          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.81/1.03      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.81/1.03  thf('57', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         ((r1_xboole_0 @ X0 @ X1)
% 0.81/1.03          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.81/1.03      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.81/1.03  thf('58', plain,
% 0.81/1.03      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.81/1.03         ((zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X13)
% 0.81/1.03          | ~ (r2_hidden @ X8 @ X13)
% 0.81/1.03          | ~ (r2_hidden @ X9 @ X11)
% 0.81/1.03          | ((X10) != (k4_tarski @ X8 @ X9)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.81/1.03  thf('59', plain,
% 0.81/1.03      (![X8 : $i, X9 : $i, X11 : $i, X13 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X9 @ X11)
% 0.81/1.03          | ~ (r2_hidden @ X8 @ X13)
% 0.81/1.03          | (zip_tseitin_0 @ X9 @ X8 @ (k4_tarski @ X8 @ X9) @ X11 @ X13))),
% 0.81/1.03      inference('simplify', [status(thm)], ['58'])).
% 0.81/1.03  thf('60', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.03         ((r1_xboole_0 @ X1 @ X0)
% 0.81/1.03          | (zip_tseitin_0 @ (sk_C @ X0 @ X1) @ X3 @ 
% 0.81/1.03             (k4_tarski @ X3 @ (sk_C @ X0 @ X1)) @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.81/1.03          | ~ (r2_hidden @ X3 @ X2))),
% 0.81/1.03      inference('sup-', [status(thm)], ['57', '59'])).
% 0.81/1.03  thf('61', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.03         ((r1_xboole_0 @ X1 @ X0)
% 0.81/1.03          | (zip_tseitin_0 @ (sk_C @ X2 @ X3) @ (sk_C @ X0 @ X1) @ 
% 0.81/1.03             (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_C @ X2 @ X3)) @ 
% 0.81/1.03             (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 0.81/1.03          | (r1_xboole_0 @ X3 @ X2))),
% 0.81/1.03      inference('sup-', [status(thm)], ['56', '60'])).
% 0.81/1.03  thf('62', plain,
% 0.81/1.03      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.81/1.03         (~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.81/1.03          | (r2_hidden @ X16 @ X19)
% 0.81/1.03          | ((X19) != (k2_zfmisc_1 @ X18 @ X17)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.81/1.03  thf('63', plain,
% 0.81/1.03      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.81/1.03         ((r2_hidden @ X16 @ (k2_zfmisc_1 @ X18 @ X17))
% 0.81/1.03          | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.81/1.03      inference('simplify', [status(thm)], ['62'])).
% 0.81/1.03  thf('64', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.03         ((r1_xboole_0 @ X3 @ X2)
% 0.81/1.03          | (r1_xboole_0 @ X1 @ X0)
% 0.81/1.03          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_C @ X2 @ X3)) @ 
% 0.81/1.03             (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['61', '63'])).
% 0.81/1.03  thf('65', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.03         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X0) @ (sk_C @ X1 @ X2)) @ 
% 0.81/1.03           (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1)))
% 0.81/1.03          | (r1_xboole_0 @ X0 @ X0)
% 0.81/1.03          | (r1_xboole_0 @ X2 @ X1))),
% 0.81/1.03      inference('sup+', [status(thm)], ['55', '64'])).
% 0.81/1.03  thf('66', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.81/1.03  thf('67', plain,
% 0.81/1.03      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.81/1.03          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.81/1.03      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.81/1.03  thf('68', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['66', '67'])).
% 0.81/1.03  thf('69', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.03         ((r1_xboole_0 @ X1 @ X0)
% 0.81/1.03          | (r1_xboole_0 @ X2 @ X2)
% 0.81/1.03          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.81/1.03               (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['65', '68'])).
% 0.81/1.03  thf('70', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         (~ (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 0.81/1.03             (k2_zfmisc_1 @ X1 @ (k3_xboole_0 @ X0 @ X0)))
% 0.81/1.03          | (r1_xboole_0 @ X1 @ X1)
% 0.81/1.03          | (r1_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['54', '69'])).
% 0.81/1.03  thf('71', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.81/1.03  thf('72', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         (~ (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0))
% 0.81/1.03          | (r1_xboole_0 @ X1 @ X1)
% 0.81/1.03          | (r1_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('demod', [status(thm)], ['70', '71'])).
% 0.81/1.03  thf('73', plain,
% 0.81/1.03      (((~ (r1_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.81/1.03         | (r1_xboole_0 @ sk_B @ sk_B)
% 0.81/1.03         | (r1_xboole_0 @ sk_A @ sk_A)))
% 0.81/1.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['42', '72'])).
% 0.81/1.03  thf('74', plain,
% 0.81/1.03      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.81/1.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('split', [status(esa)], ['30'])).
% 0.81/1.03  thf('75', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.81/1.03      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.81/1.03  thf('76', plain,
% 0.81/1.03      ((((r1_xboole_0 @ sk_B @ sk_B) | (r1_xboole_0 @ sk_A @ sk_A)))
% 0.81/1.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.81/1.03  thf('77', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.81/1.03          | ((X0) = (k1_xboole_0)))),
% 0.81/1.03      inference('demod', [status(thm)], ['25', '26'])).
% 0.81/1.03  thf('78', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['66', '67'])).
% 0.81/1.03  thf('79', plain,
% 0.81/1.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['77', '78'])).
% 0.81/1.03  thf('80', plain,
% 0.81/1.03      ((((r1_xboole_0 @ sk_A @ sk_A) | ((sk_B) = (k1_xboole_0))))
% 0.81/1.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['76', '79'])).
% 0.81/1.03  thf('81', plain,
% 0.81/1.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['77', '78'])).
% 0.81/1.03  thf('82', plain,
% 0.81/1.03      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.81/1.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['80', '81'])).
% 0.81/1.03  thf('83', plain,
% 0.81/1.03      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('split', [status(esa)], ['2'])).
% 0.81/1.03  thf('84', plain,
% 0.81/1.03      (((((sk_B) != (sk_B)) | ((sk_A) = (k1_xboole_0))))
% 0.81/1.03         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.81/1.03             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['82', '83'])).
% 0.81/1.03  thf('85', plain,
% 0.81/1.03      ((((sk_A) = (k1_xboole_0)))
% 0.81/1.03         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.81/1.03             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('simplify', [status(thm)], ['84'])).
% 0.81/1.03  thf('86', plain,
% 0.81/1.03      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.81/1.03      inference('split', [status(esa)], ['0'])).
% 0.81/1.03  thf('87', plain,
% 0.81/1.03      ((((sk_A) != (sk_A)))
% 0.81/1.03         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.81/1.03             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.81/1.03             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['85', '86'])).
% 0.81/1.03  thf('88', plain,
% 0.81/1.03      ((((sk_A) = (k1_xboole_0))) | 
% 0.81/1.03       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.81/1.03       (((sk_B) = (k1_xboole_0)))),
% 0.81/1.03      inference('simplify', [status(thm)], ['87'])).
% 0.81/1.03  thf('89', plain, (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.81/1.03      inference('sat_resolution*', [status(thm)], ['3', '40', '41', '88'])).
% 0.81/1.03  thf('90', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.81/1.03      inference('simpl_trail', [status(thm)], ['1', '89'])).
% 0.81/1.03  thf('91', plain,
% 0.81/1.03      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.03      inference('split', [status(esa)], ['30'])).
% 0.81/1.03  thf('92', plain,
% 0.81/1.03      ((((sk_A) = (k1_xboole_0))) | 
% 0.81/1.03       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.81/1.03       (((sk_B) = (k1_xboole_0)))),
% 0.81/1.03      inference('split', [status(esa)], ['30'])).
% 0.81/1.03  thf('93', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.81/1.03      inference('sat_resolution*', [status(thm)], ['3', '40', '41', '88', '92'])).
% 0.81/1.03  thf('94', plain, (((sk_A) = (k1_xboole_0))),
% 0.81/1.03      inference('simpl_trail', [status(thm)], ['91', '93'])).
% 0.81/1.03  thf('95', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (sk_A))),
% 0.81/1.03      inference('demod', [status(thm)], ['90', '94'])).
% 0.81/1.03  thf('96', plain,
% 0.81/1.03      (![X17 : $i, X18 : $i, X21 : $i]:
% 0.81/1.03         (((X21) = (k2_zfmisc_1 @ X18 @ X17))
% 0.81/1.03          | (zip_tseitin_0 @ (sk_F @ X21 @ X17 @ X18) @ 
% 0.81/1.03             (sk_E @ X21 @ X17 @ X18) @ (sk_D @ X21 @ X17 @ X18) @ X17 @ X18)
% 0.81/1.03          | (r2_hidden @ (sk_D @ X21 @ X17 @ X18) @ X21))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.81/1.03  thf('97', plain,
% 0.81/1.03      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.81/1.03         ((r2_hidden @ X8 @ X12)
% 0.81/1.03          | ~ (zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.81/1.03  thf('98', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.03         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.81/1.03          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.81/1.03          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['96', '97'])).
% 0.81/1.03  thf('99', plain,
% 0.81/1.03      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.03      inference('split', [status(esa)], ['30'])).
% 0.81/1.03  thf('100', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.81/1.03      inference('demod', [status(thm)], ['13', '14'])).
% 0.81/1.03  thf('101', plain,
% 0.81/1.03      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['99', '100'])).
% 0.81/1.03  thf('102', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.81/1.03      inference('sat_resolution*', [status(thm)], ['3', '40', '41', '88', '92'])).
% 0.81/1.03  thf('103', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.81/1.03      inference('simpl_trail', [status(thm)], ['101', '102'])).
% 0.81/1.03  thf('104', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         ((r2_hidden @ (sk_E @ sk_A @ X1 @ X0) @ X0)
% 0.81/1.03          | ((sk_A) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['98', '103'])).
% 0.81/1.03  thf('105', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.81/1.03      inference('simpl_trail', [status(thm)], ['101', '102'])).
% 0.81/1.03  thf('106', plain, (![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['104', '105'])).
% 0.81/1.03  thf('107', plain, (((sk_A) != (sk_A))),
% 0.81/1.03      inference('demod', [status(thm)], ['95', '106'])).
% 0.81/1.03  thf('108', plain, ($false), inference('simplify', [status(thm)], ['107'])).
% 0.81/1.03  
% 0.81/1.03  % SZS output end Refutation
% 0.81/1.03  
% 0.85/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
