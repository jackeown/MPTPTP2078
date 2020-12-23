%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a88ETpZjns

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:01 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 270 expanded)
%              Number of leaves         :   24 (  86 expanded)
%              Depth                    :   18
%              Number of atoms          : 1230 (3048 expanded)
%              Number of equality atoms :  146 ( 330 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('5',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
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

thf('7',plain,(
    ! [X21: $i,X22: $i,X25: $i] :
      ( ( X25
        = ( k2_zfmisc_1 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X25 @ X21 @ X22 ) @ ( sk_E @ X25 @ X21 @ X22 ) @ ( sk_D @ X25 @ X21 @ X22 ) @ X21 @ X22 )
      | ( r2_hidden @ ( sk_D @ X25 @ X21 @ X22 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ X15 )
      | ~ ( zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('17',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('31',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('35',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X0 = X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X0 = X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('41',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X17 )
      | ~ ( r2_hidden @ X12 @ X17 )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ( X14
       != ( k4_tarski @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X15: $i,X17: $i] :
      ( ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X12 @ X17 )
      | ( zip_tseitin_0 @ X13 @ X12 @ ( k4_tarski @ X12 @ X13 ) @ X15 @ X17 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( zip_tseitin_0 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X2 @ ( k4_tarski @ X2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( zip_tseitin_0 @ ( sk_C_1 @ X1 @ k1_xboole_0 ) @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ X1 @ k1_xboole_0 ) ) @ X1 @ X0 )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X20 @ X23 )
      | ( X23
       != ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X22 @ X21 ) )
      | ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X1 )
      | ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ X1 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X1 )
      | ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ X1 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('49',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X1 )
      | ( k1_xboole_0 = X0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ k1_xboole_0 ) @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X1 )
      | ( k1_xboole_0 = X0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( k1_xboole_0 = X0 )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( k1_xboole_0 = X0 )
      | ( k1_xboole_0 = X1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( k1_xboole_0 = sk_A )
      | ( k1_xboole_0 = sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','52'])).

thf('54',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('55',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_2 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('57',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_2 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('62',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['55','65'])).

thf('67',plain,
    ( ( ( k1_xboole_0 = sk_A )
      | ( k1_xboole_0 = sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54','66'])).

thf('68',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('69',plain,
    ( ( ( sk_B != sk_B )
      | ( k1_xboole_0 = sk_A ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_xboole_0 = sk_A )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('72',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('75',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('76',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('78',plain,(
    ! [X21: $i,X22: $i,X25: $i] :
      ( ( X25
        = ( k2_zfmisc_1 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X25 @ X21 @ X22 ) @ ( sk_E @ X25 @ X21 @ X22 ) @ ( sk_D @ X25 @ X21 @ X22 ) @ X21 @ X22 )
      | ( r2_hidden @ ( sk_D @ X25 @ X21 @ X22 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('79',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X12 @ X16 )
      | ~ ( zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('82',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['77','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['77','85'])).

thf('88',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','91'])).

thf('93',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('96',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('98',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('101',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','29','30','73','99','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a88ETpZjns
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:27:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.49/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.71  % Solved by: fo/fo7.sh
% 0.49/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.71  % done 332 iterations in 0.206s
% 0.49/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.71  % SZS output start Refutation
% 0.49/0.71  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.49/0.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.49/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.49/0.71  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.49/0.71  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.49/0.71  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.49/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.71  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.49/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.49/0.71  thf(t113_zfmisc_1, conjecture,
% 0.49/0.71    (![A:$i,B:$i]:
% 0.49/0.71     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.49/0.71       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.49/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.71    (~( ![A:$i,B:$i]:
% 0.49/0.71        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.49/0.71          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.49/0.71    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.49/0.71  thf('0', plain,
% 0.49/0.71      ((((sk_B) != (k1_xboole_0))
% 0.49/0.71        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('1', plain,
% 0.49/0.71      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.49/0.71       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.71      inference('split', [status(esa)], ['0'])).
% 0.49/0.71  thf('2', plain,
% 0.49/0.71      ((((sk_B) = (k1_xboole_0))
% 0.49/0.71        | ((sk_A) = (k1_xboole_0))
% 0.49/0.71        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('3', plain, ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('split', [status(esa)], ['2'])).
% 0.49/0.71  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.49/0.71  thf('4', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.49/0.71      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.71  thf('5', plain,
% 0.49/0.71      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('sup+', [status(thm)], ['3', '4'])).
% 0.49/0.71  thf('6', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.49/0.71      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.71  thf(d2_zfmisc_1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.49/0.71       ( ![D:$i]:
% 0.49/0.71         ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.71           ( ?[E:$i,F:$i]:
% 0.49/0.71             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.49/0.71               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.49/0.71  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.49/0.71  thf(zf_stmt_2, axiom,
% 0.49/0.71    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.49/0.71     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.49/0.71       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.49/0.71         ( r2_hidden @ E @ A ) ) ))).
% 0.49/0.71  thf(zf_stmt_3, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.49/0.71       ( ![D:$i]:
% 0.49/0.71         ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.71           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.49/0.71  thf('7', plain,
% 0.49/0.71      (![X21 : $i, X22 : $i, X25 : $i]:
% 0.49/0.71         (((X25) = (k2_zfmisc_1 @ X22 @ X21))
% 0.49/0.71          | (zip_tseitin_0 @ (sk_F @ X25 @ X21 @ X22) @ 
% 0.49/0.71             (sk_E @ X25 @ X21 @ X22) @ (sk_D @ X25 @ X21 @ X22) @ X21 @ X22)
% 0.49/0.71          | (r2_hidden @ (sk_D @ X25 @ X21 @ X22) @ X25))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.71  thf('8', plain,
% 0.49/0.71      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.71         ((r2_hidden @ X13 @ X15)
% 0.49/0.71          | ~ (zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.71  thf('9', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.49/0.71          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.71          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.49/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.71  thf('10', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.49/0.71          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.71          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.49/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.71  thf(t3_xboole_0, axiom,
% 0.49/0.71    (![A:$i,B:$i]:
% 0.49/0.71     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.49/0.71            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.49/0.71       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.49/0.71            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.49/0.71  thf('11', plain,
% 0.49/0.71      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X8 @ X6)
% 0.49/0.71          | ~ (r2_hidden @ X8 @ X9)
% 0.49/0.71          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.49/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.71  thf('12', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.49/0.71          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.71          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.49/0.71          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X3))),
% 0.49/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.49/0.71  thf('13', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.49/0.71          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.71          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.49/0.71          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.71          | (r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2))),
% 0.49/0.71      inference('sup-', [status(thm)], ['9', '12'])).
% 0.49/0.71  thf('14', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         (~ (r1_xboole_0 @ X0 @ X0)
% 0.49/0.71          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.71          | (r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2))),
% 0.49/0.71      inference('simplify', [status(thm)], ['13'])).
% 0.49/0.71  thf('15', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X0)
% 0.49/0.71          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['6', '14'])).
% 0.49/0.71  thf('16', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X0)
% 0.49/0.71          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['6', '14'])).
% 0.49/0.71  thf('17', plain,
% 0.49/0.71      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X8 @ X6)
% 0.49/0.71          | ~ (r2_hidden @ X8 @ X9)
% 0.49/0.71          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.49/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.71  thf('18', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 0.49/0.71          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.49/0.71          | ~ (r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X2))),
% 0.49/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.71  thf('19', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 0.49/0.71          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.49/0.71          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['15', '18'])).
% 0.49/0.71  thf('20', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (~ (r1_xboole_0 @ X0 @ X0) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.49/0.71      inference('simplify', [status(thm)], ['19'])).
% 0.49/0.71  thf('21', plain,
% 0.49/0.71      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.49/0.71         <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['5', '20'])).
% 0.49/0.71  thf('22', plain,
% 0.49/0.71      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('split', [status(esa)], ['2'])).
% 0.49/0.71  thf('23', plain,
% 0.49/0.71      ((![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.49/0.71         <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('demod', [status(thm)], ['21', '22'])).
% 0.49/0.71  thf('24', plain,
% 0.49/0.71      ((((sk_A) != (k1_xboole_0))
% 0.49/0.71        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('25', plain,
% 0.49/0.71      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.49/0.71         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('split', [status(esa)], ['24'])).
% 0.49/0.71  thf('26', plain,
% 0.49/0.71      ((((sk_B) != (k1_xboole_0)))
% 0.49/0.71         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.49/0.71             (((sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['23', '25'])).
% 0.49/0.71  thf('27', plain,
% 0.49/0.71      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('split', [status(esa)], ['2'])).
% 0.49/0.71  thf('28', plain,
% 0.49/0.71      ((((sk_B) != (sk_B)))
% 0.49/0.71         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.49/0.71             (((sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('demod', [status(thm)], ['26', '27'])).
% 0.49/0.71  thf('29', plain,
% 0.49/0.71      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.49/0.71       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.71      inference('simplify', [status(thm)], ['28'])).
% 0.49/0.71  thf('30', plain,
% 0.49/0.71      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.49/0.71       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.71      inference('split', [status(esa)], ['24'])).
% 0.49/0.71  thf('31', plain,
% 0.49/0.71      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.49/0.71         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('split', [status(esa)], ['2'])).
% 0.49/0.71  thf('32', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.49/0.71      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.71  thf(t2_tarski, axiom,
% 0.49/0.71    (![A:$i,B:$i]:
% 0.49/0.71     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.49/0.71       ( ( A ) = ( B ) ) ))).
% 0.49/0.71  thf('33', plain,
% 0.49/0.71      (![X4 : $i, X5 : $i]:
% 0.49/0.71         (((X5) = (X4))
% 0.49/0.71          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.49/0.71          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.49/0.71      inference('cnf', [status(esa)], [t2_tarski])).
% 0.49/0.71  thf('34', plain,
% 0.49/0.71      (![X4 : $i, X5 : $i]:
% 0.49/0.71         (((X5) = (X4))
% 0.49/0.71          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.49/0.71          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.49/0.71      inference('cnf', [status(esa)], [t2_tarski])).
% 0.49/0.71  thf('35', plain,
% 0.49/0.71      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X8 @ X6)
% 0.49/0.71          | ~ (r2_hidden @ X8 @ X9)
% 0.49/0.71          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.49/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.71  thf('36', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.49/0.71          | ((X0) = (X1))
% 0.49/0.71          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.49/0.71          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.49/0.71      inference('sup-', [status(thm)], ['34', '35'])).
% 0.49/0.71  thf('37', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.49/0.71          | ((X0) = (X1))
% 0.49/0.71          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.49/0.71          | ((X0) = (X1))
% 0.49/0.71          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1))),
% 0.49/0.71      inference('sup-', [status(thm)], ['33', '36'])).
% 0.49/0.71  thf('38', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (~ (r1_xboole_0 @ X0 @ X0)
% 0.49/0.71          | ((X0) = (X1))
% 0.49/0.71          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1))),
% 0.49/0.71      inference('simplify', [status(thm)], ['37'])).
% 0.49/0.71  thf('39', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.49/0.71          | ((k1_xboole_0) = (X0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['32', '38'])).
% 0.49/0.71  thf('40', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.49/0.71          | ((k1_xboole_0) = (X0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['32', '38'])).
% 0.49/0.71  thf('41', plain,
% 0.49/0.71      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 0.49/0.71         ((zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X17)
% 0.49/0.71          | ~ (r2_hidden @ X12 @ X17)
% 0.49/0.71          | ~ (r2_hidden @ X13 @ X15)
% 0.49/0.71          | ((X14) != (k4_tarski @ X12 @ X13)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.71  thf('42', plain,
% 0.49/0.71      (![X12 : $i, X13 : $i, X15 : $i, X17 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X13 @ X15)
% 0.49/0.71          | ~ (r2_hidden @ X12 @ X17)
% 0.49/0.71          | (zip_tseitin_0 @ X13 @ X12 @ (k4_tarski @ X12 @ X13) @ X15 @ X17))),
% 0.49/0.71      inference('simplify', [status(thm)], ['41'])).
% 0.49/0.71  thf('43', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         (((k1_xboole_0) = (X0))
% 0.49/0.71          | (zip_tseitin_0 @ (sk_C_1 @ X0 @ k1_xboole_0) @ X2 @ 
% 0.49/0.71             (k4_tarski @ X2 @ (sk_C_1 @ X0 @ k1_xboole_0)) @ X0 @ X1)
% 0.49/0.71          | ~ (r2_hidden @ X2 @ X1))),
% 0.49/0.71      inference('sup-', [status(thm)], ['40', '42'])).
% 0.49/0.71  thf('44', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (((k1_xboole_0) = (X0))
% 0.49/0.71          | (zip_tseitin_0 @ (sk_C_1 @ X1 @ k1_xboole_0) @ 
% 0.49/0.71             (sk_C_1 @ X0 @ k1_xboole_0) @ 
% 0.49/0.71             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ 
% 0.49/0.71              (sk_C_1 @ X1 @ k1_xboole_0)) @ 
% 0.49/0.71             X1 @ X0)
% 0.49/0.71          | ((k1_xboole_0) = (X1)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['39', '43'])).
% 0.49/0.71  thf('45', plain,
% 0.49/0.71      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.49/0.71         (~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.49/0.71          | (r2_hidden @ X20 @ X23)
% 0.49/0.71          | ((X23) != (k2_zfmisc_1 @ X22 @ X21)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.71  thf('46', plain,
% 0.49/0.71      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.49/0.71         ((r2_hidden @ X20 @ (k2_zfmisc_1 @ X22 @ X21))
% 0.49/0.71          | ~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 0.49/0.71      inference('simplify', [status(thm)], ['45'])).
% 0.49/0.71  thf('47', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (((k1_xboole_0) = (X1))
% 0.49/0.71          | ((k1_xboole_0) = (X0))
% 0.49/0.71          | (r2_hidden @ 
% 0.49/0.71             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ 
% 0.49/0.71              (sk_C_1 @ X1 @ k1_xboole_0)) @ 
% 0.49/0.71             (k2_zfmisc_1 @ X0 @ X1)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['44', '46'])).
% 0.49/0.71  thf('48', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (((k1_xboole_0) = (X1))
% 0.49/0.71          | ((k1_xboole_0) = (X0))
% 0.49/0.71          | (r2_hidden @ 
% 0.49/0.71             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ 
% 0.49/0.71              (sk_C_1 @ X1 @ k1_xboole_0)) @ 
% 0.49/0.71             (k2_zfmisc_1 @ X0 @ X1)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['44', '46'])).
% 0.49/0.71  thf('49', plain,
% 0.49/0.71      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X8 @ X6)
% 0.49/0.71          | ~ (r2_hidden @ X8 @ X9)
% 0.49/0.71          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.49/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.71  thf('50', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         (((k1_xboole_0) = (X1))
% 0.49/0.71          | ((k1_xboole_0) = (X0))
% 0.49/0.71          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 0.49/0.71          | ~ (r2_hidden @ 
% 0.49/0.71               (k4_tarski @ (sk_C_1 @ X1 @ k1_xboole_0) @ 
% 0.49/0.71                (sk_C_1 @ X0 @ k1_xboole_0)) @ 
% 0.49/0.71               X2))),
% 0.49/0.71      inference('sup-', [status(thm)], ['48', '49'])).
% 0.49/0.71  thf('51', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (((k1_xboole_0) = (X1))
% 0.49/0.71          | ((k1_xboole_0) = (X0))
% 0.49/0.71          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0))
% 0.49/0.71          | ((k1_xboole_0) = (X0))
% 0.49/0.71          | ((k1_xboole_0) = (X1)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['47', '50'])).
% 0.49/0.71  thf('52', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (~ (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0))
% 0.49/0.71          | ((k1_xboole_0) = (X0))
% 0.49/0.71          | ((k1_xboole_0) = (X1)))),
% 0.49/0.71      inference('simplify', [status(thm)], ['51'])).
% 0.49/0.71  thf('53', plain,
% 0.49/0.71      (((~ (r1_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.49/0.71         | ((k1_xboole_0) = (sk_A))
% 0.49/0.71         | ((k1_xboole_0) = (sk_B))))
% 0.49/0.71         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['31', '52'])).
% 0.49/0.71  thf('54', plain,
% 0.49/0.71      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.49/0.71         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('split', [status(esa)], ['2'])).
% 0.49/0.71  thf('55', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.49/0.71      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.71  thf('56', plain,
% 0.49/0.71      (![X6 : $i, X7 : $i]:
% 0.49/0.71         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C_2 @ X7 @ X6) @ X6))),
% 0.49/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.71  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.49/0.71  thf('57', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.49/0.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.49/0.71  thf(d3_tarski, axiom,
% 0.49/0.71    (![A:$i,B:$i]:
% 0.49/0.71     ( ( r1_tarski @ A @ B ) <=>
% 0.49/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.49/0.71  thf('58', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X0 @ X1)
% 0.49/0.71          | (r2_hidden @ X0 @ X2)
% 0.49/0.71          | ~ (r1_tarski @ X1 @ X2))),
% 0.49/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.71  thf('59', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.49/0.71      inference('sup-', [status(thm)], ['57', '58'])).
% 0.49/0.71  thf('60', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.49/0.71          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X1))),
% 0.49/0.71      inference('sup-', [status(thm)], ['56', '59'])).
% 0.49/0.71  thf('61', plain,
% 0.49/0.71      (![X6 : $i, X7 : $i]:
% 0.49/0.71         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C_2 @ X7 @ X6) @ X6))),
% 0.49/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.71  thf('62', plain,
% 0.49/0.71      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X8 @ X6)
% 0.49/0.71          | ~ (r2_hidden @ X8 @ X9)
% 0.49/0.71          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.49/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.71  thf('63', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         ((r1_xboole_0 @ X0 @ X1)
% 0.49/0.71          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.49/0.71          | ~ (r2_hidden @ (sk_C_2 @ X1 @ X0) @ X2))),
% 0.49/0.71      inference('sup-', [status(thm)], ['61', '62'])).
% 0.49/0.71  thf('64', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         ((r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.49/0.71          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.49/0.71          | (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.49/0.71      inference('sup-', [status(thm)], ['60', '63'])).
% 0.49/0.71  thf('65', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.49/0.71      inference('simplify', [status(thm)], ['64'])).
% 0.49/0.71  thf('66', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.49/0.71      inference('sup-', [status(thm)], ['55', '65'])).
% 0.49/0.71  thf('67', plain,
% 0.49/0.71      (((((k1_xboole_0) = (sk_A)) | ((k1_xboole_0) = (sk_B))))
% 0.49/0.71         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('demod', [status(thm)], ['53', '54', '66'])).
% 0.49/0.71  thf('68', plain,
% 0.49/0.71      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('split', [status(esa)], ['0'])).
% 0.49/0.71  thf('69', plain,
% 0.49/0.71      (((((sk_B) != (sk_B)) | ((k1_xboole_0) = (sk_A))))
% 0.49/0.71         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.49/0.71             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['67', '68'])).
% 0.49/0.71  thf('70', plain,
% 0.49/0.71      ((((k1_xboole_0) = (sk_A)))
% 0.49/0.71         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.49/0.71             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('simplify', [status(thm)], ['69'])).
% 0.49/0.71  thf('71', plain,
% 0.49/0.71      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.49/0.71      inference('split', [status(esa)], ['24'])).
% 0.49/0.71  thf('72', plain,
% 0.49/0.71      ((((sk_A) != (sk_A)))
% 0.49/0.71         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.49/0.71             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.49/0.71             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['70', '71'])).
% 0.49/0.71  thf('73', plain,
% 0.49/0.71      ((((sk_A) = (k1_xboole_0))) | 
% 0.49/0.71       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.49/0.71       (((sk_B) = (k1_xboole_0)))),
% 0.49/0.71      inference('simplify', [status(thm)], ['72'])).
% 0.49/0.71  thf('74', plain,
% 0.49/0.71      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.71      inference('split', [status(esa)], ['2'])).
% 0.49/0.71  thf('75', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.49/0.71      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.71  thf('76', plain,
% 0.49/0.71      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.71      inference('sup+', [status(thm)], ['74', '75'])).
% 0.49/0.71  thf('77', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.49/0.71      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.71  thf('78', plain,
% 0.49/0.71      (![X21 : $i, X22 : $i, X25 : $i]:
% 0.49/0.71         (((X25) = (k2_zfmisc_1 @ X22 @ X21))
% 0.49/0.71          | (zip_tseitin_0 @ (sk_F @ X25 @ X21 @ X22) @ 
% 0.49/0.71             (sk_E @ X25 @ X21 @ X22) @ (sk_D @ X25 @ X21 @ X22) @ X21 @ X22)
% 0.49/0.71          | (r2_hidden @ (sk_D @ X25 @ X21 @ X22) @ X25))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.71  thf('79', plain,
% 0.49/0.71      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.71         ((r2_hidden @ X12 @ X16)
% 0.49/0.71          | ~ (zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.71  thf('80', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.49/0.71          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.71          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.49/0.71      inference('sup-', [status(thm)], ['78', '79'])).
% 0.49/0.71  thf('81', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.49/0.71          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.71          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.49/0.71      inference('sup-', [status(thm)], ['78', '79'])).
% 0.49/0.71  thf('82', plain,
% 0.49/0.71      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X8 @ X6)
% 0.49/0.71          | ~ (r2_hidden @ X8 @ X9)
% 0.49/0.71          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.49/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.71  thf('83', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 0.49/0.71          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.71          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.49/0.71          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X3))),
% 0.49/0.71      inference('sup-', [status(thm)], ['81', '82'])).
% 0.49/0.71  thf('84', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 0.49/0.71          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.71          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.49/0.71          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.71          | (r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1))),
% 0.49/0.71      inference('sup-', [status(thm)], ['80', '83'])).
% 0.49/0.71  thf('85', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         (~ (r1_xboole_0 @ X0 @ X0)
% 0.49/0.71          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.71          | (r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1))),
% 0.49/0.71      inference('simplify', [status(thm)], ['84'])).
% 0.49/0.71  thf('86', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.49/0.71          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['77', '85'])).
% 0.49/0.71  thf('87', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.49/0.71          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['77', '85'])).
% 0.49/0.71  thf('88', plain,
% 0.49/0.71      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X8 @ X6)
% 0.49/0.71          | ~ (r2_hidden @ X8 @ X9)
% 0.49/0.71          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.49/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.71  thf('89', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.71          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.49/0.71          | ~ (r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X2))),
% 0.49/0.71      inference('sup-', [status(thm)], ['87', '88'])).
% 0.49/0.71  thf('90', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.71          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.49/0.71          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['86', '89'])).
% 0.49/0.71  thf('91', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (~ (r1_xboole_0 @ X0 @ X0) | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.49/0.71      inference('simplify', [status(thm)], ['90'])).
% 0.49/0.71  thf('92', plain,
% 0.49/0.71      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.49/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['76', '91'])).
% 0.49/0.71  thf('93', plain,
% 0.49/0.71      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.71      inference('split', [status(esa)], ['2'])).
% 0.49/0.71  thf('94', plain,
% 0.49/0.71      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.49/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.71      inference('demod', [status(thm)], ['92', '93'])).
% 0.49/0.71  thf('95', plain,
% 0.49/0.71      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.49/0.71         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.71      inference('split', [status(esa)], ['24'])).
% 0.49/0.71  thf('96', plain,
% 0.49/0.71      ((((sk_A) != (k1_xboole_0)))
% 0.49/0.71         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.49/0.71             (((sk_A) = (k1_xboole_0))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['94', '95'])).
% 0.49/0.71  thf('97', plain,
% 0.49/0.71      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.71      inference('split', [status(esa)], ['2'])).
% 0.49/0.71  thf('98', plain,
% 0.49/0.71      ((((sk_A) != (sk_A)))
% 0.49/0.71         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.49/0.71             (((sk_A) = (k1_xboole_0))))),
% 0.49/0.71      inference('demod', [status(thm)], ['96', '97'])).
% 0.49/0.71  thf('99', plain,
% 0.49/0.71      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.49/0.71       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.71      inference('simplify', [status(thm)], ['98'])).
% 0.49/0.71  thf('100', plain,
% 0.49/0.71      ((((sk_A) = (k1_xboole_0))) | 
% 0.49/0.71       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.49/0.71       (((sk_B) = (k1_xboole_0)))),
% 0.49/0.71      inference('split', [status(esa)], ['2'])).
% 0.49/0.71  thf('101', plain, ($false),
% 0.49/0.71      inference('sat_resolution*', [status(thm)],
% 0.49/0.71                ['1', '29', '30', '73', '99', '100'])).
% 0.49/0.71  
% 0.49/0.71  % SZS output end Refutation
% 0.49/0.71  
% 0.49/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
