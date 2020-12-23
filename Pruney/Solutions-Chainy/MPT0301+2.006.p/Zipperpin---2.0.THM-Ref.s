%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1dnHCBKHn8

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:00 EST 2020

% Result     : Theorem 43.81s
% Output     : Refutation 43.81s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 422 expanded)
%              Number of leaves         :   34 ( 135 expanded)
%              Depth                    :   18
%              Number of atoms          : 1076 (3439 expanded)
%              Number of equality atoms :  149 ( 489 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
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
    ! [X35: $i,X36: $i,X39: $i] :
      ( ( X39
        = ( k2_zfmisc_1 @ X36 @ X35 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X39 @ X35 @ X36 ) @ ( sk_E @ X39 @ X35 @ X36 ) @ ( sk_D @ X39 @ X35 @ X36 ) @ X35 @ X36 )
      | ( r2_hidden @ ( sk_D @ X39 @ X35 @ X36 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X27 @ X29 )
      | ~ ( zip_tseitin_0 @ X27 @ X26 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','15'])).

thf('21',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( sk_B_1
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('29',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['25'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X27 @ X26 @ X28 @ X29 @ X31 )
      | ~ ( r2_hidden @ X26 @ X31 )
      | ~ ( r2_hidden @ X27 @ X29 )
      | ( X28
       != ( k4_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('35',plain,(
    ! [X26: $i,X27: $i,X29: $i,X31: $i] :
      ( ~ ( r2_hidden @ X27 @ X29 )
      | ~ ( r2_hidden @ X26 @ X31 )
      | ( zip_tseitin_0 @ X27 @ X26 @ ( k4_tarski @ X26 @ X27 ) @ X29 @ X31 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ X3 @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_C @ X2 @ X1 ) @ ( sk_B @ X0 ) @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ X1 @ X0 )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('39',plain,(
    ! [X35: $i,X36: $i,X39: $i] :
      ( ( X39
        = ( k2_zfmisc_1 @ X36 @ X35 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X39 @ X35 @ X36 ) @ ( sk_E @ X39 @ X35 @ X36 ) @ ( sk_D @ X39 @ X35 @ X36 ) @ X35 @ X36 )
      | ( r2_hidden @ ( sk_D @ X39 @ X35 @ X36 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X34 @ X37 )
      | ( X37
       != ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X34 @ ( k2_zfmisc_1 @ X36 @ X35 ) )
      | ~ ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 )
        | ( X0
          = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','42'])).

thf('44',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 )
        | ( X0 = k1_xboole_0 )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','15'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('48',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('49',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ X0 )
          = k1_xboole_0 )
        | ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_B_1 @ sk_A )
          = X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('51',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('52',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('53',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X48 ) @ X49 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_B_1 @ sk_A )
        = X0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X35: $i,X36: $i,X39: $i,X40: $i,X41: $i] :
      ( ( X39
        = ( k2_zfmisc_1 @ X36 @ X35 ) )
      | ~ ( zip_tseitin_0 @ X40 @ X41 @ ( sk_D @ X39 @ X35 @ X36 ) @ X35 @ X36 )
      | ~ ( r2_hidden @ ( sk_D @ X39 @ X35 @ X36 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_B_1 @ sk_A )
        | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ sk_B_1 @ sk_A ) @ ( k1_tarski @ X0 ) )
        | ( ( k1_tarski @ X0 )
          = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_B_1 @ sk_A )
        = X0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['50','55'])).

thf('60',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('61',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('63',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_B_1 @ sk_A )
        | ( ( k1_tarski @ X0 )
          = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('65',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_B_1 @ sk_A )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B_1 @ X0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('68',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('71',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','70'])).

thf('72',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['69','71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['68','72'])).

thf('74',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['25'])).

thf('75',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('78',plain,(
    ! [X35: $i,X36: $i,X39: $i] :
      ( ( X39
        = ( k2_zfmisc_1 @ X36 @ X35 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X39 @ X35 @ X36 ) @ ( sk_E @ X39 @ X35 @ X36 ) @ ( sk_D @ X39 @ X35 @ X36 ) @ X35 @ X36 )
      | ( r2_hidden @ ( sk_D @ X39 @ X35 @ X36 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('79',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X26 @ X30 )
      | ~ ( zip_tseitin_0 @ X27 @ X26 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','15'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('84',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','15'])).

thf('85',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['25'])).

thf('90',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('92',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','30','31','76','77','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1dnHCBKHn8
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 43.81/44.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 43.81/44.00  % Solved by: fo/fo7.sh
% 43.81/44.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 43.81/44.00  % done 27361 iterations in 43.551s
% 43.81/44.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 43.81/44.00  % SZS output start Refutation
% 43.81/44.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 43.81/44.00  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 43.81/44.00  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 43.81/44.00  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 43.81/44.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 43.81/44.00  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 43.81/44.00  thf(sk_B_type, type, sk_B: $i > $i).
% 43.81/44.00  thf(sk_B_1_type, type, sk_B_1: $i).
% 43.81/44.00  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 43.81/44.00  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 43.81/44.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 43.81/44.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 43.81/44.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 43.81/44.00  thf(sk_A_type, type, sk_A: $i).
% 43.81/44.00  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 43.81/44.00  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 43.81/44.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 43.81/44.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 43.81/44.00  thf(t113_zfmisc_1, conjecture,
% 43.81/44.00    (![A:$i,B:$i]:
% 43.81/44.00     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 43.81/44.00       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 43.81/44.00  thf(zf_stmt_0, negated_conjecture,
% 43.81/44.00    (~( ![A:$i,B:$i]:
% 43.81/44.00        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 43.81/44.00          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 43.81/44.00    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 43.81/44.00  thf('0', plain,
% 43.81/44.00      ((((sk_B_1) != (k1_xboole_0))
% 43.81/44.00        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 43.81/44.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.81/44.00  thf('1', plain,
% 43.81/44.00      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 43.81/44.00       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 43.81/44.00      inference('split', [status(esa)], ['0'])).
% 43.81/44.00  thf(d2_zfmisc_1, axiom,
% 43.81/44.00    (![A:$i,B:$i,C:$i]:
% 43.81/44.00     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 43.81/44.00       ( ![D:$i]:
% 43.81/44.00         ( ( r2_hidden @ D @ C ) <=>
% 43.81/44.00           ( ?[E:$i,F:$i]:
% 43.81/44.00             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 43.81/44.00               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 43.81/44.00  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 43.81/44.00  thf(zf_stmt_2, axiom,
% 43.81/44.00    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 43.81/44.00     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 43.81/44.00       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 43.81/44.00         ( r2_hidden @ E @ A ) ) ))).
% 43.81/44.00  thf(zf_stmt_3, axiom,
% 43.81/44.00    (![A:$i,B:$i,C:$i]:
% 43.81/44.00     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 43.81/44.00       ( ![D:$i]:
% 43.81/44.00         ( ( r2_hidden @ D @ C ) <=>
% 43.81/44.00           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 43.81/44.00  thf('2', plain,
% 43.81/44.00      (![X35 : $i, X36 : $i, X39 : $i]:
% 43.81/44.00         (((X39) = (k2_zfmisc_1 @ X36 @ X35))
% 43.81/44.00          | (zip_tseitin_0 @ (sk_F @ X39 @ X35 @ X36) @ 
% 43.81/44.00             (sk_E @ X39 @ X35 @ X36) @ (sk_D @ X39 @ X35 @ X36) @ X35 @ X36)
% 43.81/44.00          | (r2_hidden @ (sk_D @ X39 @ X35 @ X36) @ X39))),
% 43.81/44.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 43.81/44.00  thf('3', plain,
% 43.81/44.00      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 43.81/44.00         ((r2_hidden @ X27 @ X29)
% 43.81/44.00          | ~ (zip_tseitin_0 @ X27 @ X26 @ X28 @ X29 @ X30))),
% 43.81/44.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 43.81/44.00  thf('4', plain,
% 43.81/44.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.81/44.00         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 43.81/44.00          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 43.81/44.00          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 43.81/44.00      inference('sup-', [status(thm)], ['2', '3'])).
% 43.81/44.00  thf(t17_xboole_1, axiom,
% 43.81/44.00    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 43.81/44.00  thf('5', plain,
% 43.81/44.00      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 43.81/44.00      inference('cnf', [status(esa)], [t17_xboole_1])).
% 43.81/44.00  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 43.81/44.00  thf('6', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 43.81/44.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 43.81/44.00  thf(d10_xboole_0, axiom,
% 43.81/44.00    (![A:$i,B:$i]:
% 43.81/44.00     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 43.81/44.00  thf('7', plain,
% 43.81/44.00      (![X12 : $i, X14 : $i]:
% 43.81/44.00         (((X12) = (X14))
% 43.81/44.00          | ~ (r1_tarski @ X14 @ X12)
% 43.81/44.00          | ~ (r1_tarski @ X12 @ X14))),
% 43.81/44.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 43.81/44.00  thf('8', plain,
% 43.81/44.00      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 43.81/44.00      inference('sup-', [status(thm)], ['6', '7'])).
% 43.81/44.00  thf('9', plain,
% 43.81/44.00      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 43.81/44.00      inference('sup-', [status(thm)], ['5', '8'])).
% 43.81/44.00  thf(t4_xboole_0, axiom,
% 43.81/44.00    (![A:$i,B:$i]:
% 43.81/44.00     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 43.81/44.00            ( r1_xboole_0 @ A @ B ) ) ) & 
% 43.81/44.00       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 43.81/44.00            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 43.81/44.00  thf('10', plain,
% 43.81/44.00      (![X7 : $i, X9 : $i, X10 : $i]:
% 43.81/44.00         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 43.81/44.00          | ~ (r1_xboole_0 @ X7 @ X10))),
% 43.81/44.00      inference('cnf', [status(esa)], [t4_xboole_0])).
% 43.81/44.00  thf('11', plain,
% 43.81/44.00      (![X0 : $i, X1 : $i]:
% 43.81/44.00         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 43.81/44.00      inference('sup-', [status(thm)], ['9', '10'])).
% 43.81/44.00  thf('12', plain,
% 43.81/44.00      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 43.81/44.00      inference('sup-', [status(thm)], ['5', '8'])).
% 43.81/44.00  thf(d7_xboole_0, axiom,
% 43.81/44.00    (![A:$i,B:$i]:
% 43.81/44.00     ( ( r1_xboole_0 @ A @ B ) <=>
% 43.81/44.00       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 43.81/44.00  thf('13', plain,
% 43.81/44.00      (![X4 : $i, X6 : $i]:
% 43.81/44.00         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 43.81/44.00      inference('cnf', [status(esa)], [d7_xboole_0])).
% 43.81/44.00  thf('14', plain,
% 43.81/44.00      (![X0 : $i]:
% 43.81/44.00         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 43.81/44.00      inference('sup-', [status(thm)], ['12', '13'])).
% 43.81/44.00  thf('15', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 43.81/44.00      inference('simplify', [status(thm)], ['14'])).
% 43.81/44.00  thf('16', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 43.81/44.00      inference('demod', [status(thm)], ['11', '15'])).
% 43.81/44.00  thf('17', plain,
% 43.81/44.00      (![X0 : $i, X1 : $i]:
% 43.81/44.00         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 43.81/44.00          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 43.81/44.00      inference('sup-', [status(thm)], ['4', '16'])).
% 43.81/44.00  thf('18', plain,
% 43.81/44.00      ((((sk_B_1) = (k1_xboole_0))
% 43.81/44.00        | ((sk_A) = (k1_xboole_0))
% 43.81/44.00        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 43.81/44.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.81/44.00  thf('19', plain,
% 43.81/44.00      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('split', [status(esa)], ['18'])).
% 43.81/44.00  thf('20', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 43.81/44.00      inference('demod', [status(thm)], ['11', '15'])).
% 43.81/44.00  thf('21', plain,
% 43.81/44.00      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1))
% 43.81/44.00         <= ((((sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('sup-', [status(thm)], ['19', '20'])).
% 43.81/44.00  thf('22', plain,
% 43.81/44.00      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 43.81/44.00         <= ((((sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('sup-', [status(thm)], ['17', '21'])).
% 43.81/44.00  thf('23', plain,
% 43.81/44.00      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('split', [status(esa)], ['18'])).
% 43.81/44.00  thf('24', plain,
% 43.81/44.00      ((![X0 : $i]: ((sk_B_1) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 43.81/44.00         <= ((((sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('demod', [status(thm)], ['22', '23'])).
% 43.81/44.00  thf('25', plain,
% 43.81/44.00      ((((sk_A) != (k1_xboole_0))
% 43.81/44.00        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 43.81/44.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.81/44.00  thf('26', plain,
% 43.81/44.00      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 43.81/44.00         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('split', [status(esa)], ['25'])).
% 43.81/44.00  thf('27', plain,
% 43.81/44.00      ((((sk_B_1) != (k1_xboole_0)))
% 43.81/44.00         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 43.81/44.00             (((sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('sup-', [status(thm)], ['24', '26'])).
% 43.81/44.00  thf('28', plain,
% 43.81/44.00      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('split', [status(esa)], ['18'])).
% 43.81/44.00  thf('29', plain,
% 43.81/44.00      ((((sk_B_1) != (sk_B_1)))
% 43.81/44.00         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 43.81/44.00             (((sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('demod', [status(thm)], ['27', '28'])).
% 43.81/44.00  thf('30', plain,
% 43.81/44.00      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 43.81/44.00       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 43.81/44.00      inference('simplify', [status(thm)], ['29'])).
% 43.81/44.00  thf('31', plain,
% 43.81/44.00      (~ (((sk_A) = (k1_xboole_0))) | 
% 43.81/44.00       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 43.81/44.00      inference('split', [status(esa)], ['25'])).
% 43.81/44.00  thf(t7_xboole_0, axiom,
% 43.81/44.00    (![A:$i]:
% 43.81/44.00     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 43.81/44.00          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 43.81/44.00  thf('32', plain,
% 43.81/44.00      (![X11 : $i]:
% 43.81/44.00         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 43.81/44.00      inference('cnf', [status(esa)], [t7_xboole_0])).
% 43.81/44.00  thf(d3_tarski, axiom,
% 43.81/44.00    (![A:$i,B:$i]:
% 43.81/44.00     ( ( r1_tarski @ A @ B ) <=>
% 43.81/44.00       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 43.81/44.00  thf('33', plain,
% 43.81/44.00      (![X1 : $i, X3 : $i]:
% 43.81/44.00         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 43.81/44.00      inference('cnf', [status(esa)], [d3_tarski])).
% 43.81/44.00  thf('34', plain,
% 43.81/44.00      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 43.81/44.00         ((zip_tseitin_0 @ X27 @ X26 @ X28 @ X29 @ X31)
% 43.81/44.00          | ~ (r2_hidden @ X26 @ X31)
% 43.81/44.00          | ~ (r2_hidden @ X27 @ X29)
% 43.81/44.00          | ((X28) != (k4_tarski @ X26 @ X27)))),
% 43.81/44.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 43.81/44.00  thf('35', plain,
% 43.81/44.00      (![X26 : $i, X27 : $i, X29 : $i, X31 : $i]:
% 43.81/44.00         (~ (r2_hidden @ X27 @ X29)
% 43.81/44.00          | ~ (r2_hidden @ X26 @ X31)
% 43.81/44.00          | (zip_tseitin_0 @ X27 @ X26 @ (k4_tarski @ X26 @ X27) @ X29 @ X31))),
% 43.81/44.00      inference('simplify', [status(thm)], ['34'])).
% 43.81/44.00  thf('36', plain,
% 43.81/44.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 43.81/44.00         ((r1_tarski @ X0 @ X1)
% 43.81/44.00          | (zip_tseitin_0 @ (sk_C @ X1 @ X0) @ X3 @ 
% 43.81/44.00             (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ X0 @ X2)
% 43.81/44.00          | ~ (r2_hidden @ X3 @ X2))),
% 43.81/44.00      inference('sup-', [status(thm)], ['33', '35'])).
% 43.81/44.00  thf('37', plain,
% 43.81/44.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.81/44.00         (((X0) = (k1_xboole_0))
% 43.81/44.00          | (zip_tseitin_0 @ (sk_C @ X2 @ X1) @ (sk_B @ X0) @ 
% 43.81/44.00             (k4_tarski @ (sk_B @ X0) @ (sk_C @ X2 @ X1)) @ X1 @ X0)
% 43.81/44.00          | (r1_tarski @ X1 @ X2))),
% 43.81/44.00      inference('sup-', [status(thm)], ['32', '36'])).
% 43.81/44.00  thf('38', plain,
% 43.81/44.00      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('split', [status(esa)], ['18'])).
% 43.81/44.00  thf('39', plain,
% 43.81/44.00      (![X35 : $i, X36 : $i, X39 : $i]:
% 43.81/44.00         (((X39) = (k2_zfmisc_1 @ X36 @ X35))
% 43.81/44.00          | (zip_tseitin_0 @ (sk_F @ X39 @ X35 @ X36) @ 
% 43.81/44.00             (sk_E @ X39 @ X35 @ X36) @ (sk_D @ X39 @ X35 @ X36) @ X35 @ X36)
% 43.81/44.00          | (r2_hidden @ (sk_D @ X39 @ X35 @ X36) @ X39))),
% 43.81/44.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 43.81/44.00  thf('40', plain,
% 43.81/44.00      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 43.81/44.00         (~ (zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36)
% 43.81/44.00          | (r2_hidden @ X34 @ X37)
% 43.81/44.00          | ((X37) != (k2_zfmisc_1 @ X36 @ X35)))),
% 43.81/44.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 43.81/44.00  thf('41', plain,
% 43.81/44.00      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 43.81/44.00         ((r2_hidden @ X34 @ (k2_zfmisc_1 @ X36 @ X35))
% 43.81/44.00          | ~ (zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 43.81/44.00      inference('simplify', [status(thm)], ['40'])).
% 43.81/44.00  thf('42', plain,
% 43.81/44.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.81/44.00         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 43.81/44.00          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 43.81/44.00          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 43.81/44.00      inference('sup-', [status(thm)], ['39', '41'])).
% 43.81/44.00  thf('43', plain,
% 43.81/44.00      ((![X0 : $i]:
% 43.81/44.00          ((r2_hidden @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ k1_xboole_0)
% 43.81/44.00           | ((X0) = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 43.81/44.00           | (r2_hidden @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X0)))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('sup+', [status(thm)], ['38', '42'])).
% 43.81/44.00  thf('44', plain,
% 43.81/44.00      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('split', [status(esa)], ['18'])).
% 43.81/44.00  thf('45', plain,
% 43.81/44.00      ((![X0 : $i]:
% 43.81/44.00          ((r2_hidden @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ k1_xboole_0)
% 43.81/44.00           | ((X0) = (k1_xboole_0))
% 43.81/44.00           | (r2_hidden @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X0)))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('demod', [status(thm)], ['43', '44'])).
% 43.81/44.00  thf('46', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 43.81/44.00      inference('demod', [status(thm)], ['11', '15'])).
% 43.81/44.00  thf('47', plain,
% 43.81/44.00      ((![X0 : $i]:
% 43.81/44.00          ((r2_hidden @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X0)
% 43.81/44.00           | ((X0) = (k1_xboole_0))))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('clc', [status(thm)], ['45', '46'])).
% 43.81/44.00  thf(d1_tarski, axiom,
% 43.81/44.00    (![A:$i,B:$i]:
% 43.81/44.00     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 43.81/44.00       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 43.81/44.00  thf('48', plain,
% 43.81/44.00      (![X18 : $i, X20 : $i, X21 : $i]:
% 43.81/44.00         (~ (r2_hidden @ X21 @ X20)
% 43.81/44.00          | ((X21) = (X18))
% 43.81/44.00          | ((X20) != (k1_tarski @ X18)))),
% 43.81/44.00      inference('cnf', [status(esa)], [d1_tarski])).
% 43.81/44.00  thf('49', plain,
% 43.81/44.00      (![X18 : $i, X21 : $i]:
% 43.81/44.00         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 43.81/44.00      inference('simplify', [status(thm)], ['48'])).
% 43.81/44.00  thf('50', plain,
% 43.81/44.00      ((![X0 : $i]:
% 43.81/44.00          (((k1_tarski @ X0) = (k1_xboole_0))
% 43.81/44.00           | ((sk_D @ (k1_tarski @ X0) @ sk_B_1 @ sk_A) = (X0))))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('sup-', [status(thm)], ['47', '49'])).
% 43.81/44.00  thf(t69_enumset1, axiom,
% 43.81/44.00    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 43.81/44.00  thf('51', plain,
% 43.81/44.00      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 43.81/44.00      inference('cnf', [status(esa)], [t69_enumset1])).
% 43.81/44.00  thf(t41_enumset1, axiom,
% 43.81/44.00    (![A:$i,B:$i]:
% 43.81/44.00     ( ( k2_tarski @ A @ B ) =
% 43.81/44.00       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 43.81/44.00  thf('52', plain,
% 43.81/44.00      (![X23 : $i, X24 : $i]:
% 43.81/44.00         ((k2_tarski @ X23 @ X24)
% 43.81/44.00           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X24)))),
% 43.81/44.00      inference('cnf', [status(esa)], [t41_enumset1])).
% 43.81/44.00  thf(t49_zfmisc_1, axiom,
% 43.81/44.00    (![A:$i,B:$i]:
% 43.81/44.00     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 43.81/44.00  thf('53', plain,
% 43.81/44.00      (![X48 : $i, X49 : $i]:
% 43.81/44.00         ((k2_xboole_0 @ (k1_tarski @ X48) @ X49) != (k1_xboole_0))),
% 43.81/44.00      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 43.81/44.00  thf('54', plain,
% 43.81/44.00      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 43.81/44.00      inference('sup-', [status(thm)], ['52', '53'])).
% 43.81/44.00  thf('55', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 43.81/44.00      inference('sup-', [status(thm)], ['51', '54'])).
% 43.81/44.00  thf('56', plain,
% 43.81/44.00      ((![X0 : $i]: ((sk_D @ (k1_tarski @ X0) @ sk_B_1 @ sk_A) = (X0)))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('simplify_reflect-', [status(thm)], ['50', '55'])).
% 43.81/44.00  thf('57', plain,
% 43.81/44.00      (![X35 : $i, X36 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 43.81/44.00         (((X39) = (k2_zfmisc_1 @ X36 @ X35))
% 43.81/44.00          | ~ (zip_tseitin_0 @ X40 @ X41 @ (sk_D @ X39 @ X35 @ X36) @ X35 @ X36)
% 43.81/44.00          | ~ (r2_hidden @ (sk_D @ X39 @ X35 @ X36) @ X39))),
% 43.81/44.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 43.81/44.00  thf('58', plain,
% 43.81/44.00      ((![X0 : $i, X1 : $i, X2 : $i]:
% 43.81/44.00          (~ (zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_B_1 @ sk_A)
% 43.81/44.00           | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ sk_B_1 @ sk_A) @ 
% 43.81/44.00                (k1_tarski @ X0))
% 43.81/44.00           | ((k1_tarski @ X0) = (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('sup-', [status(thm)], ['56', '57'])).
% 43.81/44.00  thf('59', plain,
% 43.81/44.00      ((![X0 : $i]: ((sk_D @ (k1_tarski @ X0) @ sk_B_1 @ sk_A) = (X0)))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('simplify_reflect-', [status(thm)], ['50', '55'])).
% 43.81/44.00  thf('60', plain,
% 43.81/44.00      (![X18 : $i, X19 : $i, X20 : $i]:
% 43.81/44.00         (((X19) != (X18))
% 43.81/44.00          | (r2_hidden @ X19 @ X20)
% 43.81/44.00          | ((X20) != (k1_tarski @ X18)))),
% 43.81/44.00      inference('cnf', [status(esa)], [d1_tarski])).
% 43.81/44.00  thf('61', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 43.81/44.00      inference('simplify', [status(thm)], ['60'])).
% 43.81/44.00  thf('62', plain,
% 43.81/44.00      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('split', [status(esa)], ['18'])).
% 43.81/44.00  thf('63', plain,
% 43.81/44.00      ((![X0 : $i, X1 : $i, X2 : $i]:
% 43.81/44.00          (~ (zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_B_1 @ sk_A)
% 43.81/44.00           | ((k1_tarski @ X0) = (k1_xboole_0))))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('demod', [status(thm)], ['58', '59', '61', '62'])).
% 43.81/44.00  thf('64', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 43.81/44.00      inference('sup-', [status(thm)], ['51', '54'])).
% 43.81/44.00  thf('65', plain,
% 43.81/44.00      ((![X0 : $i, X1 : $i, X2 : $i]:
% 43.81/44.00          ~ (zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_B_1 @ sk_A))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 43.81/44.00  thf('66', plain,
% 43.81/44.00      ((![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ((sk_A) = (k1_xboole_0))))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('sup-', [status(thm)], ['37', '65'])).
% 43.81/44.00  thf('67', plain,
% 43.81/44.00      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 43.81/44.00      inference('sup-', [status(thm)], ['6', '7'])).
% 43.81/44.00  thf('68', plain,
% 43.81/44.00      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('sup-', [status(thm)], ['66', '67'])).
% 43.81/44.00  thf('69', plain,
% 43.81/44.00      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('split', [status(esa)], ['0'])).
% 43.81/44.00  thf('70', plain,
% 43.81/44.00      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 43.81/44.00       ~ (((sk_B_1) = (k1_xboole_0)))),
% 43.81/44.00      inference('simplify', [status(thm)], ['29'])).
% 43.81/44.00  thf('71', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 43.81/44.00      inference('sat_resolution*', [status(thm)], ['1', '70'])).
% 43.81/44.00  thf('72', plain, (((sk_B_1) != (k1_xboole_0))),
% 43.81/44.00      inference('simpl_trail', [status(thm)], ['69', '71'])).
% 43.81/44.00  thf('73', plain,
% 43.81/44.00      ((((sk_A) = (k1_xboole_0)))
% 43.81/44.00         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('simplify_reflect-', [status(thm)], ['68', '72'])).
% 43.81/44.00  thf('74', plain,
% 43.81/44.00      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 43.81/44.00      inference('split', [status(esa)], ['25'])).
% 43.81/44.00  thf('75', plain,
% 43.81/44.00      ((((sk_A) != (sk_A)))
% 43.81/44.00         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 43.81/44.00             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('sup-', [status(thm)], ['73', '74'])).
% 43.81/44.00  thf('76', plain,
% 43.81/44.00      ((((sk_A) = (k1_xboole_0))) | 
% 43.81/44.00       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 43.81/44.00      inference('simplify', [status(thm)], ['75'])).
% 43.81/44.00  thf('77', plain,
% 43.81/44.00      ((((sk_A) = (k1_xboole_0))) | 
% 43.81/44.00       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 43.81/44.00       (((sk_B_1) = (k1_xboole_0)))),
% 43.81/44.00      inference('split', [status(esa)], ['18'])).
% 43.81/44.00  thf('78', plain,
% 43.81/44.00      (![X35 : $i, X36 : $i, X39 : $i]:
% 43.81/44.00         (((X39) = (k2_zfmisc_1 @ X36 @ X35))
% 43.81/44.00          | (zip_tseitin_0 @ (sk_F @ X39 @ X35 @ X36) @ 
% 43.81/44.00             (sk_E @ X39 @ X35 @ X36) @ (sk_D @ X39 @ X35 @ X36) @ X35 @ X36)
% 43.81/44.00          | (r2_hidden @ (sk_D @ X39 @ X35 @ X36) @ X39))),
% 43.81/44.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 43.81/44.00  thf('79', plain,
% 43.81/44.00      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 43.81/44.00         ((r2_hidden @ X26 @ X30)
% 43.81/44.00          | ~ (zip_tseitin_0 @ X27 @ X26 @ X28 @ X29 @ X30))),
% 43.81/44.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 43.81/44.00  thf('80', plain,
% 43.81/44.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.81/44.00         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 43.81/44.00          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 43.81/44.00          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 43.81/44.00      inference('sup-', [status(thm)], ['78', '79'])).
% 43.81/44.00  thf('81', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 43.81/44.00      inference('demod', [status(thm)], ['11', '15'])).
% 43.81/44.00  thf('82', plain,
% 43.81/44.00      (![X0 : $i, X1 : $i]:
% 43.81/44.00         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 43.81/44.00          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 43.81/44.00      inference('sup-', [status(thm)], ['80', '81'])).
% 43.81/44.00  thf('83', plain,
% 43.81/44.00      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 43.81/44.00      inference('split', [status(esa)], ['18'])).
% 43.81/44.00  thf('84', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 43.81/44.00      inference('demod', [status(thm)], ['11', '15'])).
% 43.81/44.00  thf('85', plain,
% 43.81/44.00      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 43.81/44.00      inference('sup-', [status(thm)], ['83', '84'])).
% 43.81/44.00  thf('86', plain,
% 43.81/44.00      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 43.81/44.00         <= ((((sk_A) = (k1_xboole_0))))),
% 43.81/44.00      inference('sup-', [status(thm)], ['82', '85'])).
% 43.81/44.00  thf('87', plain,
% 43.81/44.00      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 43.81/44.00      inference('split', [status(esa)], ['18'])).
% 43.81/44.00  thf('88', plain,
% 43.81/44.00      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 43.81/44.00         <= ((((sk_A) = (k1_xboole_0))))),
% 43.81/44.00      inference('demod', [status(thm)], ['86', '87'])).
% 43.81/44.00  thf('89', plain,
% 43.81/44.00      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 43.81/44.00         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 43.81/44.00      inference('split', [status(esa)], ['25'])).
% 43.81/44.00  thf('90', plain,
% 43.81/44.00      ((((sk_A) != (k1_xboole_0)))
% 43.81/44.00         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 43.81/44.00             (((sk_A) = (k1_xboole_0))))),
% 43.81/44.00      inference('sup-', [status(thm)], ['88', '89'])).
% 43.81/44.00  thf('91', plain,
% 43.81/44.00      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 43.81/44.00      inference('split', [status(esa)], ['18'])).
% 43.81/44.00  thf('92', plain,
% 43.81/44.00      ((((sk_A) != (sk_A)))
% 43.81/44.00         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 43.81/44.00             (((sk_A) = (k1_xboole_0))))),
% 43.81/44.00      inference('demod', [status(thm)], ['90', '91'])).
% 43.81/44.00  thf('93', plain,
% 43.81/44.00      (~ (((sk_A) = (k1_xboole_0))) | 
% 43.81/44.00       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 43.81/44.00      inference('simplify', [status(thm)], ['92'])).
% 43.81/44.00  thf('94', plain, ($false),
% 43.81/44.00      inference('sat_resolution*', [status(thm)],
% 43.81/44.00                ['1', '30', '31', '76', '77', '93'])).
% 43.81/44.00  
% 43.81/44.00  % SZS output end Refutation
% 43.81/44.00  
% 43.81/44.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
