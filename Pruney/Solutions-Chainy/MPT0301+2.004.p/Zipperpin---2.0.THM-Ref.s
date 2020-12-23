%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FL5BsmBK5o

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:59 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 331 expanded)
%              Number of leaves         :   23 ( 104 expanded)
%              Depth                    :   17
%              Number of atoms          :  905 (2861 expanded)
%              Number of equality atoms :  124 ( 431 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

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

thf('2',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ( X23
        = ( k2_zfmisc_1 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X23 @ X19 @ X20 ) @ ( sk_E @ X23 @ X19 @ X20 ) @ ( sk_D @ X23 @ X19 @ X20 ) @ X19 @ X20 )
      | ( r2_hidden @ ( sk_D @ X23 @ X19 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X13 )
      | ~ ( zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k5_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( sk_F @ sk_B @ X1 @ X0 ) @ X1 )
        | ( sk_B
          = ( k2_zfmisc_1 @ X0 @ X1 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('26',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('29',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('30',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('31',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ( X23
        = ( k2_zfmisc_1 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X23 @ X19 @ X20 ) @ ( sk_E @ X23 @ X19 @ X20 ) @ ( sk_D @ X23 @ X19 @ X20 ) @ X19 @ X20 )
      | ( r2_hidden @ ( sk_D @ X23 @ X19 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X18 @ X21 )
      | ( X21
       != ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X20 @ X19 ) )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ k1_xboole_0 )
        | ( X0
          = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ k1_xboole_0 )
        | ( X0 = k1_xboole_0 )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X15 )
      | ~ ( r2_hidden @ X10 @ X15 )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ( X12
       != ( k4_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('42',plain,(
    ! [X10: $i,X11: $i,X13: $i,X15: $i] :
      ( ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r2_hidden @ X10 @ X15 )
      | ( zip_tseitin_0 @ X11 @ X10 @ ( k4_tarski @ X10 @ X11 ) @ X13 @ X15 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( X0 = k1_xboole_0 )
        | ( zip_tseitin_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X2 @ ( k4_tarski @ X2 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) @ X0 @ X1 )
        | ~ ( r2_hidden @ X2 @ X1 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 = k1_xboole_0 )
        | ( zip_tseitin_0 @ ( sk_D @ X1 @ sk_B @ sk_A ) @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k4_tarski @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( sk_D @ X1 @ sk_B @ sk_A ) ) @ X1 @ X0 )
        | ( X1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X20 @ X19 ) )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('46',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X1 = k1_xboole_0 )
        | ( X0 = k1_xboole_0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( sk_D @ X1 @ sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','46'])).

thf('48',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('50',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','49'])).

thf('51',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['48','50'])).

thf('52',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('56',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('59',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ( X23
        = ( k2_zfmisc_1 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X23 @ X19 @ X20 ) @ ( sk_E @ X23 @ X19 @ X20 ) @ ( sk_D @ X23 @ X19 @ X20 ) @ X19 @ X20 )
      | ( r2_hidden @ ( sk_D @ X23 @ X19 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X10 @ X14 )
      | ~ ( zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('65',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('66',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('71',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('73',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','57','58','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FL5BsmBK5o
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:26:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.78  % Solved by: fo/fo7.sh
% 0.54/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.78  % done 634 iterations in 0.340s
% 0.54/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.78  % SZS output start Refutation
% 0.54/0.78  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.78  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.54/0.78  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.54/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.54/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.78  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.54/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.78  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.54/0.78  thf(t113_zfmisc_1, conjecture,
% 0.54/0.78    (![A:$i,B:$i]:
% 0.54/0.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.78    (~( ![A:$i,B:$i]:
% 0.54/0.78        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.78          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.54/0.78    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.78  thf('0', plain,
% 0.54/0.78      ((((sk_B) != (k1_xboole_0))
% 0.54/0.78        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('1', plain,
% 0.54/0.78      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.54/0.78       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.54/0.78      inference('split', [status(esa)], ['0'])).
% 0.54/0.78  thf(d2_zfmisc_1, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i]:
% 0.54/0.78     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.54/0.78       ( ![D:$i]:
% 0.54/0.78         ( ( r2_hidden @ D @ C ) <=>
% 0.54/0.78           ( ?[E:$i,F:$i]:
% 0.54/0.78             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.54/0.78               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.54/0.78  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.54/0.78  thf(zf_stmt_2, axiom,
% 0.54/0.78    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.54/0.78     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.54/0.78       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.54/0.78         ( r2_hidden @ E @ A ) ) ))).
% 0.54/0.78  thf(zf_stmt_3, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i]:
% 0.54/0.78     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.54/0.78       ( ![D:$i]:
% 0.54/0.78         ( ( r2_hidden @ D @ C ) <=>
% 0.54/0.78           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.54/0.78  thf('2', plain,
% 0.54/0.78      (![X19 : $i, X20 : $i, X23 : $i]:
% 0.54/0.78         (((X23) = (k2_zfmisc_1 @ X20 @ X19))
% 0.54/0.78          | (zip_tseitin_0 @ (sk_F @ X23 @ X19 @ X20) @ 
% 0.54/0.78             (sk_E @ X23 @ X19 @ X20) @ (sk_D @ X23 @ X19 @ X20) @ X19 @ X20)
% 0.54/0.78          | (r2_hidden @ (sk_D @ X23 @ X19 @ X20) @ X23))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.78  thf('3', plain,
% 0.54/0.78      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.54/0.78         ((r2_hidden @ X11 @ X13)
% 0.54/0.78          | ~ (zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X14))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.78  thf('4', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.78         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.54/0.78          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.54/0.78          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.54/0.78      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.78  thf('5', plain,
% 0.54/0.78      ((((sk_B) = (k1_xboole_0))
% 0.54/0.78        | ((sk_A) = (k1_xboole_0))
% 0.54/0.78        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('6', plain, ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('split', [status(esa)], ['5'])).
% 0.54/0.78  thf(commutativity_k3_xboole_0, axiom,
% 0.54/0.78    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.54/0.78  thf('7', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.78  thf(t2_boole, axiom,
% 0.54/0.78    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.54/0.78  thf('8', plain,
% 0.54/0.78      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.78      inference('cnf', [status(esa)], [t2_boole])).
% 0.54/0.78  thf('9', plain,
% 0.54/0.78      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.54/0.78      inference('sup+', [status(thm)], ['7', '8'])).
% 0.54/0.78  thf(t4_xboole_0, axiom,
% 0.54/0.78    (![A:$i,B:$i]:
% 0.54/0.78     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.54/0.78            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.54/0.78       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.54/0.78            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.54/0.78  thf('10', plain,
% 0.54/0.78      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.54/0.78         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.54/0.78          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.54/0.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.54/0.78  thf('11', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i]:
% 0.54/0.78         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.54/0.78      inference('sup-', [status(thm)], ['9', '10'])).
% 0.54/0.78  thf('12', plain,
% 0.54/0.78      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.78      inference('cnf', [status(esa)], [t2_boole])).
% 0.54/0.78  thf(l97_xboole_1, axiom,
% 0.54/0.78    (![A:$i,B:$i]:
% 0.54/0.78     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.54/0.78  thf('13', plain,
% 0.54/0.78      (![X6 : $i, X7 : $i]:
% 0.54/0.78         (r1_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k5_xboole_0 @ X6 @ X7))),
% 0.54/0.78      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.54/0.78  thf('14', plain,
% 0.54/0.78      (![X0 : $i]:
% 0.54/0.78         (r1_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.78      inference('sup+', [status(thm)], ['12', '13'])).
% 0.54/0.78  thf(t5_boole, axiom,
% 0.54/0.78    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.78  thf('15', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.54/0.78      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.78  thf('16', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.54/0.78      inference('demod', [status(thm)], ['14', '15'])).
% 0.54/0.78  thf('17', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.54/0.78      inference('demod', [status(thm)], ['11', '16'])).
% 0.54/0.78  thf('18', plain,
% 0.54/0.78      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('sup-', [status(thm)], ['6', '17'])).
% 0.54/0.78  thf('19', plain,
% 0.54/0.78      ((![X0 : $i, X1 : $i]:
% 0.54/0.78          ((r2_hidden @ (sk_F @ sk_B @ X1 @ X0) @ X1)
% 0.54/0.78           | ((sk_B) = (k2_zfmisc_1 @ X0 @ X1))))
% 0.54/0.78         <= ((((sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('sup-', [status(thm)], ['4', '18'])).
% 0.54/0.78  thf('20', plain,
% 0.54/0.78      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('sup-', [status(thm)], ['6', '17'])).
% 0.54/0.78  thf('21', plain,
% 0.54/0.78      ((![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.54/0.78         <= ((((sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.78  thf('22', plain,
% 0.54/0.78      ((((sk_A) != (k1_xboole_0))
% 0.54/0.78        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('23', plain,
% 0.54/0.78      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.54/0.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('split', [status(esa)], ['22'])).
% 0.54/0.78  thf('24', plain,
% 0.54/0.78      ((((sk_B) != (k1_xboole_0)))
% 0.54/0.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.54/0.78             (((sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('sup-', [status(thm)], ['21', '23'])).
% 0.54/0.78  thf('25', plain,
% 0.54/0.78      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('split', [status(esa)], ['5'])).
% 0.54/0.78  thf('26', plain,
% 0.54/0.78      ((((sk_B) != (sk_B)))
% 0.54/0.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.54/0.78             (((sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('demod', [status(thm)], ['24', '25'])).
% 0.54/0.78  thf('27', plain,
% 0.54/0.78      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.54/0.78       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.54/0.78      inference('simplify', [status(thm)], ['26'])).
% 0.54/0.78  thf('28', plain,
% 0.54/0.78      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.54/0.78       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.54/0.78      inference('split', [status(esa)], ['22'])).
% 0.54/0.78  thf('29', plain,
% 0.54/0.78      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.54/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('split', [status(esa)], ['5'])).
% 0.54/0.78  thf('30', plain,
% 0.54/0.78      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.54/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('split', [status(esa)], ['5'])).
% 0.54/0.78  thf('31', plain,
% 0.54/0.78      (![X19 : $i, X20 : $i, X23 : $i]:
% 0.54/0.78         (((X23) = (k2_zfmisc_1 @ X20 @ X19))
% 0.54/0.78          | (zip_tseitin_0 @ (sk_F @ X23 @ X19 @ X20) @ 
% 0.54/0.78             (sk_E @ X23 @ X19 @ X20) @ (sk_D @ X23 @ X19 @ X20) @ X19 @ X20)
% 0.54/0.78          | (r2_hidden @ (sk_D @ X23 @ X19 @ X20) @ X23))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.78  thf('32', plain,
% 0.54/0.78      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.54/0.78         (~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.54/0.78          | (r2_hidden @ X18 @ X21)
% 0.54/0.78          | ((X21) != (k2_zfmisc_1 @ X20 @ X19)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.78  thf('33', plain,
% 0.54/0.78      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.78         ((r2_hidden @ X18 @ (k2_zfmisc_1 @ X20 @ X19))
% 0.54/0.78          | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.54/0.78      inference('simplify', [status(thm)], ['32'])).
% 0.54/0.78  thf('34', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.78         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.54/0.78          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.54/0.78          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.54/0.78      inference('sup-', [status(thm)], ['31', '33'])).
% 0.54/0.78  thf('35', plain,
% 0.54/0.78      ((![X0 : $i]:
% 0.54/0.78          ((r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ k1_xboole_0)
% 0.54/0.78           | ((X0) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.54/0.78           | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)))
% 0.54/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('sup+', [status(thm)], ['30', '34'])).
% 0.54/0.78  thf('36', plain,
% 0.54/0.78      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.54/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('split', [status(esa)], ['5'])).
% 0.54/0.78  thf('37', plain,
% 0.54/0.78      ((![X0 : $i]:
% 0.54/0.78          ((r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ k1_xboole_0)
% 0.54/0.78           | ((X0) = (k1_xboole_0))
% 0.54/0.78           | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)))
% 0.54/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('demod', [status(thm)], ['35', '36'])).
% 0.54/0.78  thf('38', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.54/0.78      inference('demod', [status(thm)], ['11', '16'])).
% 0.54/0.78  thf('39', plain,
% 0.54/0.78      ((![X0 : $i]:
% 0.54/0.78          ((r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 0.54/0.78           | ((X0) = (k1_xboole_0))))
% 0.54/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('clc', [status(thm)], ['37', '38'])).
% 0.54/0.78  thf('40', plain,
% 0.54/0.78      ((![X0 : $i]:
% 0.54/0.78          ((r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 0.54/0.78           | ((X0) = (k1_xboole_0))))
% 0.54/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('clc', [status(thm)], ['37', '38'])).
% 0.54/0.78  thf('41', plain,
% 0.54/0.78      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 0.54/0.78         ((zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X15)
% 0.54/0.78          | ~ (r2_hidden @ X10 @ X15)
% 0.54/0.78          | ~ (r2_hidden @ X11 @ X13)
% 0.54/0.78          | ((X12) != (k4_tarski @ X10 @ X11)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.78  thf('42', plain,
% 0.54/0.78      (![X10 : $i, X11 : $i, X13 : $i, X15 : $i]:
% 0.54/0.78         (~ (r2_hidden @ X11 @ X13)
% 0.54/0.78          | ~ (r2_hidden @ X10 @ X15)
% 0.54/0.78          | (zip_tseitin_0 @ X11 @ X10 @ (k4_tarski @ X10 @ X11) @ X13 @ X15))),
% 0.54/0.78      inference('simplify', [status(thm)], ['41'])).
% 0.54/0.78  thf('43', plain,
% 0.54/0.78      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.78          (((X0) = (k1_xboole_0))
% 0.54/0.78           | (zip_tseitin_0 @ (sk_D @ X0 @ sk_B @ sk_A) @ X2 @ 
% 0.54/0.78              (k4_tarski @ X2 @ (sk_D @ X0 @ sk_B @ sk_A)) @ X0 @ X1)
% 0.54/0.78           | ~ (r2_hidden @ X2 @ X1)))
% 0.54/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('sup-', [status(thm)], ['40', '42'])).
% 0.54/0.78  thf('44', plain,
% 0.54/0.78      ((![X0 : $i, X1 : $i]:
% 0.54/0.78          (((X0) = (k1_xboole_0))
% 0.54/0.78           | (zip_tseitin_0 @ (sk_D @ X1 @ sk_B @ sk_A) @ 
% 0.54/0.78              (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.54/0.78              (k4_tarski @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.54/0.78               (sk_D @ X1 @ sk_B @ sk_A)) @ 
% 0.54/0.78              X1 @ X0)
% 0.54/0.78           | ((X1) = (k1_xboole_0))))
% 0.54/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('sup-', [status(thm)], ['39', '43'])).
% 0.54/0.78  thf('45', plain,
% 0.54/0.78      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.78         ((r2_hidden @ X18 @ (k2_zfmisc_1 @ X20 @ X19))
% 0.54/0.78          | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.54/0.78      inference('simplify', [status(thm)], ['32'])).
% 0.54/0.78  thf('46', plain,
% 0.54/0.78      ((![X0 : $i, X1 : $i]:
% 0.54/0.78          (((X1) = (k1_xboole_0))
% 0.54/0.78           | ((X0) = (k1_xboole_0))
% 0.54/0.78           | (r2_hidden @ 
% 0.54/0.78              (k4_tarski @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.54/0.78               (sk_D @ X1 @ sk_B @ sk_A)) @ 
% 0.54/0.78              (k2_zfmisc_1 @ X0 @ X1))))
% 0.54/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('sup-', [status(thm)], ['44', '45'])).
% 0.54/0.78  thf('47', plain,
% 0.54/0.78      ((((r2_hidden @ 
% 0.54/0.78          (k4_tarski @ (sk_D @ sk_A @ sk_B @ sk_A) @ 
% 0.54/0.78           (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.54/0.78          k1_xboole_0)
% 0.54/0.78         | ((sk_A) = (k1_xboole_0))
% 0.54/0.78         | ((sk_B) = (k1_xboole_0))))
% 0.54/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('sup+', [status(thm)], ['29', '46'])).
% 0.54/0.78  thf('48', plain,
% 0.54/0.78      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('split', [status(esa)], ['0'])).
% 0.54/0.78  thf('49', plain,
% 0.54/0.78      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.54/0.78       ~ (((sk_B) = (k1_xboole_0)))),
% 0.54/0.78      inference('simplify', [status(thm)], ['26'])).
% 0.54/0.78  thf('50', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.54/0.78      inference('sat_resolution*', [status(thm)], ['1', '49'])).
% 0.54/0.78  thf('51', plain, (((sk_B) != (k1_xboole_0))),
% 0.54/0.78      inference('simpl_trail', [status(thm)], ['48', '50'])).
% 0.54/0.78  thf('52', plain,
% 0.54/0.78      ((((r2_hidden @ 
% 0.54/0.78          (k4_tarski @ (sk_D @ sk_A @ sk_B @ sk_A) @ 
% 0.54/0.78           (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.54/0.78          k1_xboole_0)
% 0.54/0.78         | ((sk_A) = (k1_xboole_0))))
% 0.54/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('simplify_reflect-', [status(thm)], ['47', '51'])).
% 0.54/0.78  thf('53', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.54/0.78      inference('demod', [status(thm)], ['11', '16'])).
% 0.54/0.78  thf('54', plain,
% 0.54/0.78      ((((sk_A) = (k1_xboole_0)))
% 0.54/0.78         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('clc', [status(thm)], ['52', '53'])).
% 0.54/0.78  thf('55', plain,
% 0.54/0.78      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.54/0.78      inference('split', [status(esa)], ['22'])).
% 0.54/0.78  thf('56', plain,
% 0.54/0.78      ((((sk_A) != (sk_A)))
% 0.54/0.78         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 0.54/0.78             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('sup-', [status(thm)], ['54', '55'])).
% 0.54/0.78  thf('57', plain,
% 0.54/0.78      ((((sk_A) = (k1_xboole_0))) | 
% 0.54/0.78       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.54/0.78      inference('simplify', [status(thm)], ['56'])).
% 0.54/0.78  thf('58', plain,
% 0.54/0.78      ((((sk_A) = (k1_xboole_0))) | 
% 0.54/0.78       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.54/0.78       (((sk_B) = (k1_xboole_0)))),
% 0.54/0.78      inference('split', [status(esa)], ['5'])).
% 0.54/0.78  thf('59', plain,
% 0.54/0.78      (![X19 : $i, X20 : $i, X23 : $i]:
% 0.54/0.78         (((X23) = (k2_zfmisc_1 @ X20 @ X19))
% 0.54/0.78          | (zip_tseitin_0 @ (sk_F @ X23 @ X19 @ X20) @ 
% 0.54/0.78             (sk_E @ X23 @ X19 @ X20) @ (sk_D @ X23 @ X19 @ X20) @ X19 @ X20)
% 0.54/0.78          | (r2_hidden @ (sk_D @ X23 @ X19 @ X20) @ X23))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.78  thf('60', plain,
% 0.54/0.78      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.54/0.78         ((r2_hidden @ X10 @ X14)
% 0.54/0.78          | ~ (zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X14))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.78  thf('61', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.78         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.54/0.78          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.54/0.78          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.54/0.78      inference('sup-', [status(thm)], ['59', '60'])).
% 0.54/0.78  thf('62', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.54/0.78      inference('demod', [status(thm)], ['11', '16'])).
% 0.54/0.78  thf('63', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i]:
% 0.54/0.78         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.54/0.78          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.54/0.78      inference('sup-', [status(thm)], ['61', '62'])).
% 0.54/0.78  thf('64', plain,
% 0.54/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.78      inference('split', [status(esa)], ['5'])).
% 0.54/0.78  thf('65', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.54/0.78      inference('demod', [status(thm)], ['11', '16'])).
% 0.54/0.78  thf('66', plain,
% 0.54/0.78      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.78      inference('sup-', [status(thm)], ['64', '65'])).
% 0.54/0.78  thf('67', plain,
% 0.54/0.78      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.54/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.78      inference('sup-', [status(thm)], ['63', '66'])).
% 0.54/0.78  thf('68', plain,
% 0.54/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.78      inference('split', [status(esa)], ['5'])).
% 0.54/0.78  thf('69', plain,
% 0.54/0.78      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.54/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.78      inference('demod', [status(thm)], ['67', '68'])).
% 0.54/0.78  thf('70', plain,
% 0.54/0.78      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.54/0.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.78      inference('split', [status(esa)], ['22'])).
% 0.54/0.78  thf('71', plain,
% 0.54/0.78      ((((sk_A) != (k1_xboole_0)))
% 0.54/0.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.54/0.78             (((sk_A) = (k1_xboole_0))))),
% 0.54/0.78      inference('sup-', [status(thm)], ['69', '70'])).
% 0.54/0.78  thf('72', plain,
% 0.54/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.78      inference('split', [status(esa)], ['5'])).
% 0.54/0.78  thf('73', plain,
% 0.54/0.78      ((((sk_A) != (sk_A)))
% 0.54/0.78         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.54/0.78             (((sk_A) = (k1_xboole_0))))),
% 0.54/0.78      inference('demod', [status(thm)], ['71', '72'])).
% 0.54/0.78  thf('74', plain,
% 0.54/0.78      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.54/0.78       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.54/0.78      inference('simplify', [status(thm)], ['73'])).
% 0.54/0.78  thf('75', plain, ($false),
% 0.54/0.78      inference('sat_resolution*', [status(thm)],
% 0.54/0.78                ['1', '27', '28', '57', '58', '74'])).
% 0.54/0.78  
% 0.54/0.78  % SZS output end Refutation
% 0.54/0.78  
% 0.62/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
