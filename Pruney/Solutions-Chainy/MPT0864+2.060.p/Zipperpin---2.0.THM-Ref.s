%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Sx7nys0N3w

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:07 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 222 expanded)
%              Number of leaves         :   40 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  873 (1884 expanded)
%              Number of equality atoms :  120 ( 284 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X10 @ X10 @ X11 @ X12 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k4_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
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
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 )
      | ( r2_hidden @ X48 @ X55 )
      | ( X55
       != ( k4_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( r2_hidden @ X48 @ ( k4_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 ) )
      | ( zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X41 != X40 )
      | ~ ( zip_tseitin_0 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X40: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ~ ( zip_tseitin_0 @ X40 @ X42 @ X43 @ X44 @ X45 @ X46 @ X40 ) ),
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
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X28 ) @ X30 )
      | ~ ( r2_hidden @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

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

thf('18',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('19',plain,(
    ! [X60: $i,X62: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X60 @ X62 ) )
      = X62 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('20',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('26',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X36 ) @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_tarski @ ( k4_tarski @ X36 @ X37 ) @ ( k4_tarski @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ X0 ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ sk_A ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','27'])).

thf('29',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('30',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('33',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('34',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X34 != X33 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X33 ) )
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('35',plain,(
    ! [X33: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X33 ) )
     != ( k1_tarski @ X33 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('39',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('40',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('42',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('47',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X33: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X33 ) ) ),
    inference(demod,[status(thm)],['35','38','48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','49'])).

thf('51',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('53',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('54',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X60 @ X61 ) )
      = X60 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('56',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('58',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X36 ) @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_tarski @ ( k4_tarski @ X36 @ X37 ) @ ( k4_tarski @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ X0 ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
      = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','62'])).

thf('64',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('65',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('66',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('68',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X33: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X33 ) ) ),
    inference(demod,[status(thm)],['35','38','48'])).

thf('70',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','70'])).

thf('72',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('73',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['51','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Sx7nys0N3w
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.87  % Solved by: fo/fo7.sh
% 0.68/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.87  % done 874 iterations in 0.414s
% 0.68/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.87  % SZS output start Refutation
% 0.68/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.68/0.87  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.68/0.87  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.87  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.68/0.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.87  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.68/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.87  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.68/0.87  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.68/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.68/0.87  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.68/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.87  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(t70_enumset1, axiom,
% 0.68/0.87    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.68/0.87  thf('0', plain,
% 0.68/0.87      (![X8 : $i, X9 : $i]:
% 0.68/0.87         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 0.68/0.87      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.68/0.87  thf(t69_enumset1, axiom,
% 0.68/0.87    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.68/0.87  thf('1', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.68/0.87      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.68/0.87  thf('2', plain,
% 0.68/0.87      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['0', '1'])).
% 0.68/0.87  thf(t71_enumset1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.68/0.87  thf('3', plain,
% 0.68/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.68/0.87         ((k2_enumset1 @ X10 @ X10 @ X11 @ X12)
% 0.68/0.87           = (k1_enumset1 @ X10 @ X11 @ X12))),
% 0.68/0.87      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.68/0.87  thf(t72_enumset1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.87     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.68/0.87  thf('4', plain,
% 0.68/0.87      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.87         ((k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16)
% 0.68/0.87           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.68/0.87      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.68/0.87  thf(t73_enumset1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.68/0.87     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.68/0.87       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.68/0.87  thf('5', plain,
% 0.68/0.87      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.68/0.87         ((k4_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.68/0.87           = (k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.68/0.87      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.68/0.87  thf(d4_enumset1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.68/0.87     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.68/0.87       ( ![H:$i]:
% 0.68/0.87         ( ( r2_hidden @ H @ G ) <=>
% 0.68/0.87           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.68/0.87                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.68/0.87  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.68/0.87  thf(zf_stmt_1, axiom,
% 0.68/0.87    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.68/0.87     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.68/0.87       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.68/0.87         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.68/0.87  thf(zf_stmt_2, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.68/0.87     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.68/0.87       ( ![H:$i]:
% 0.68/0.87         ( ( r2_hidden @ H @ G ) <=>
% 0.68/0.87           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.68/0.87  thf('6', plain,
% 0.68/0.87      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, 
% 0.68/0.87         X55 : $i]:
% 0.68/0.87         ((zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54)
% 0.68/0.87          | (r2_hidden @ X48 @ X55)
% 0.68/0.87          | ((X55) != (k4_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.68/0.87  thf('7', plain,
% 0.68/0.87      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.68/0.87         ((r2_hidden @ X48 @ (k4_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49))
% 0.68/0.87          | (zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 0.68/0.87      inference('simplify', [status(thm)], ['6'])).
% 0.68/0.87  thf('8', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.68/0.87         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.68/0.87          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.68/0.87      inference('sup+', [status(thm)], ['5', '7'])).
% 0.68/0.87  thf('9', plain,
% 0.68/0.87      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.68/0.87         (((X41) != (X40))
% 0.68/0.87          | ~ (zip_tseitin_0 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X40))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.68/0.87  thf('10', plain,
% 0.68/0.87      (![X40 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.68/0.87         ~ (zip_tseitin_0 @ X40 @ X42 @ X43 @ X44 @ X45 @ X46 @ X40)),
% 0.68/0.87      inference('simplify', [status(thm)], ['9'])).
% 0.68/0.87  thf('11', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.68/0.87         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.68/0.87      inference('sup-', [status(thm)], ['8', '10'])).
% 0.68/0.87  thf('12', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.87         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['4', '11'])).
% 0.68/0.87  thf('13', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['3', '12'])).
% 0.68/0.87  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['2', '13'])).
% 0.68/0.87  thf(l1_zfmisc_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.68/0.87  thf('15', plain,
% 0.68/0.87      (![X28 : $i, X30 : $i]:
% 0.68/0.87         ((r1_tarski @ (k1_tarski @ X28) @ X30) | ~ (r2_hidden @ X28 @ X30))),
% 0.68/0.87      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.68/0.87  thf('16', plain,
% 0.68/0.87      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.68/0.87      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.87  thf('17', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.68/0.87      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.68/0.87  thf(t20_mcart_1, conjecture,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.68/0.87       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.68/0.87  thf(zf_stmt_3, negated_conjecture,
% 0.68/0.87    (~( ![A:$i]:
% 0.68/0.87        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.68/0.87          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.68/0.87    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.68/0.87  thf('18', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.87  thf(t7_mcart_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.68/0.87       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.68/0.87  thf('19', plain,
% 0.68/0.87      (![X60 : $i, X62 : $i]: ((k2_mcart_1 @ (k4_tarski @ X60 @ X62)) = (X62))),
% 0.68/0.87      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.68/0.87  thf('20', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.68/0.87      inference('sup+', [status(thm)], ['18', '19'])).
% 0.68/0.87  thf('21', plain,
% 0.68/0.87      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.87  thf('22', plain,
% 0.68/0.87      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('split', [status(esa)], ['21'])).
% 0.68/0.87  thf('23', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['20', '22'])).
% 0.68/0.87  thf('24', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.87  thf('25', plain,
% 0.68/0.87      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.68/0.87         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['23', '24'])).
% 0.68/0.87  thf(t36_zfmisc_1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.68/0.87         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.68/0.87       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.68/0.87         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.68/0.87  thf('26', plain,
% 0.68/0.87      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.68/0.87         ((k2_zfmisc_1 @ (k1_tarski @ X36) @ (k2_tarski @ X37 @ X38))
% 0.68/0.87           = (k2_tarski @ (k4_tarski @ X36 @ X37) @ (k4_tarski @ X36 @ X38)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.68/0.87  thf('27', plain,
% 0.68/0.87      ((![X0 : $i]:
% 0.68/0.87          ((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_A @ X0))
% 0.68/0.87            = (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ X0))))
% 0.68/0.87         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['25', '26'])).
% 0.68/0.87  thf('28', plain,
% 0.68/0.87      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.68/0.87          = (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ sk_A))))
% 0.68/0.87         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['17', '27'])).
% 0.68/0.87  thf('29', plain,
% 0.68/0.87      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.68/0.87         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['23', '24'])).
% 0.68/0.87  thf('30', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.68/0.87      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.68/0.87  thf('31', plain,
% 0.68/0.87      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.68/0.87          = (k1_tarski @ sk_A)))
% 0.68/0.87         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.68/0.87  thf(t135_zfmisc_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.68/0.87         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.68/0.87       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.68/0.87  thf('32', plain,
% 0.68/0.87      (![X31 : $i, X32 : $i]:
% 0.68/0.87         (((X31) = (k1_xboole_0))
% 0.68/0.87          | ~ (r1_tarski @ X31 @ (k2_zfmisc_1 @ X32 @ X31)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.68/0.87  thf('33', plain,
% 0.68/0.87      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.68/0.87         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.68/0.87         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('sup-', [status(thm)], ['31', '32'])).
% 0.68/0.87  thf(t20_zfmisc_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.68/0.87         ( k1_tarski @ A ) ) <=>
% 0.68/0.87       ( ( A ) != ( B ) ) ))).
% 0.68/0.87  thf('34', plain,
% 0.68/0.87      (![X33 : $i, X34 : $i]:
% 0.68/0.87         (((X34) != (X33))
% 0.68/0.87          | ((k4_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X33))
% 0.68/0.87              != (k1_tarski @ X34)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.68/0.87  thf('35', plain,
% 0.68/0.87      (![X33 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X33))
% 0.68/0.87           != (k1_tarski @ X33))),
% 0.68/0.87      inference('simplify', [status(thm)], ['34'])).
% 0.68/0.87  thf(idempotence_k3_xboole_0, axiom,
% 0.68/0.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.68/0.87  thf('36', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.68/0.87      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.68/0.87  thf(t100_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.68/0.87  thf('37', plain,
% 0.68/0.87      (![X1 : $i, X2 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ X1 @ X2)
% 0.68/0.87           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.87  thf('38', plain,
% 0.68/0.87      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['36', '37'])).
% 0.68/0.87  thf(t2_boole, axiom,
% 0.68/0.87    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.68/0.87  thf('39', plain,
% 0.68/0.87      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.87      inference('cnf', [status(esa)], [t2_boole])).
% 0.68/0.87  thf('40', plain,
% 0.68/0.87      (![X1 : $i, X2 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ X1 @ X2)
% 0.68/0.87           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.87  thf('41', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['39', '40'])).
% 0.68/0.87  thf(t5_boole, axiom,
% 0.68/0.87    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.68/0.87  thf('42', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.68/0.87      inference('cnf', [status(esa)], [t5_boole])).
% 0.68/0.87  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.68/0.87      inference('demod', [status(thm)], ['41', '42'])).
% 0.68/0.87  thf(t48_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.68/0.87  thf('44', plain,
% 0.68/0.87      (![X4 : $i, X5 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.68/0.87           = (k3_xboole_0 @ X4 @ X5))),
% 0.68/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.87  thf('45', plain,
% 0.68/0.87      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['43', '44'])).
% 0.68/0.87  thf('46', plain,
% 0.68/0.87      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['36', '37'])).
% 0.68/0.87  thf('47', plain,
% 0.68/0.87      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.87      inference('cnf', [status(esa)], [t2_boole])).
% 0.68/0.87  thf('48', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.87      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.68/0.87  thf('49', plain, (![X33 : $i]: ((k1_xboole_0) != (k1_tarski @ X33))),
% 0.68/0.87      inference('demod', [status(thm)], ['35', '38', '48'])).
% 0.68/0.87  thf('50', plain,
% 0.68/0.87      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.68/0.87         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('clc', [status(thm)], ['33', '49'])).
% 0.68/0.87  thf('51', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('sup-', [status(thm)], ['16', '50'])).
% 0.68/0.87  thf('52', plain,
% 0.68/0.87      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.68/0.87      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.87  thf('53', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.68/0.87      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.68/0.87  thf('54', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.87  thf('55', plain,
% 0.68/0.87      (![X60 : $i, X61 : $i]: ((k1_mcart_1 @ (k4_tarski @ X60 @ X61)) = (X60))),
% 0.68/0.87      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.68/0.87  thf('56', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.68/0.87      inference('sup+', [status(thm)], ['54', '55'])).
% 0.68/0.87  thf('57', plain,
% 0.68/0.87      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('split', [status(esa)], ['21'])).
% 0.68/0.87  thf('58', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['56', '57'])).
% 0.68/0.87  thf('59', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.87  thf('60', plain,
% 0.68/0.87      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.68/0.87         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['58', '59'])).
% 0.68/0.87  thf('61', plain,
% 0.68/0.87      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.68/0.87         ((k2_zfmisc_1 @ (k1_tarski @ X36) @ (k2_tarski @ X37 @ X38))
% 0.68/0.87           = (k2_tarski @ (k4_tarski @ X36 @ X37) @ (k4_tarski @ X36 @ X38)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.68/0.87  thf('62', plain,
% 0.68/0.87      ((![X0 : $i]:
% 0.68/0.87          ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ X0))
% 0.68/0.87            = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ X0))))
% 0.68/0.87         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['60', '61'])).
% 0.68/0.87  thf('63', plain,
% 0.68/0.87      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.68/0.87          = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ sk_C))))
% 0.68/0.87         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['53', '62'])).
% 0.68/0.87  thf('64', plain,
% 0.68/0.87      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.68/0.87         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['58', '59'])).
% 0.68/0.87  thf('65', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.68/0.87      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.68/0.87  thf('66', plain,
% 0.68/0.87      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.68/0.87          = (k1_tarski @ sk_A)))
% 0.68/0.87         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.68/0.87  thf('67', plain,
% 0.68/0.87      (![X31 : $i, X32 : $i]:
% 0.68/0.87         (((X31) = (k1_xboole_0))
% 0.68/0.87          | ~ (r1_tarski @ X31 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.68/0.87  thf('68', plain,
% 0.68/0.87      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.68/0.87         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.68/0.87         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('sup-', [status(thm)], ['66', '67'])).
% 0.68/0.87  thf('69', plain, (![X33 : $i]: ((k1_xboole_0) != (k1_tarski @ X33))),
% 0.68/0.87      inference('demod', [status(thm)], ['35', '38', '48'])).
% 0.68/0.87  thf('70', plain,
% 0.68/0.87      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.68/0.87         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.68/0.87      inference('clc', [status(thm)], ['68', '69'])).
% 0.68/0.87  thf('71', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['52', '70'])).
% 0.68/0.87  thf('72', plain,
% 0.68/0.87      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.68/0.87      inference('split', [status(esa)], ['21'])).
% 0.68/0.87  thf('73', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.68/0.87      inference('sat_resolution*', [status(thm)], ['71', '72'])).
% 0.68/0.87  thf('74', plain, ($false),
% 0.68/0.87      inference('simpl_trail', [status(thm)], ['51', '73'])).
% 0.68/0.87  
% 0.68/0.87  % SZS output end Refutation
% 0.68/0.87  
% 0.68/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
