%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iXazbxW9RO

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 197 expanded)
%              Number of leaves         :   40 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :  873 (1788 expanded)
%              Number of equality atoms :  114 ( 259 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k5_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(d5_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( H
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) )
    <=> ! [I: $i] :
          ( ( r2_hidden @ I @ H )
        <=> ~ ( ( I != G )
              & ( I != F )
              & ( I != E )
              & ( I != D )
              & ( I != C )
              & ( I != B )
              & ( I != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [I: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( I != A )
        & ( I != B )
        & ( I != C )
        & ( I != D )
        & ( I != E )
        & ( I != F )
        & ( I != G ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( H
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) )
    <=> ! [I: $i] :
          ( ( r2_hidden @ I @ H )
        <=> ~ ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( zip_tseitin_0 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 )
      | ( r2_hidden @ X53 @ X61 )
      | ( X61
       != ( k5_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( r2_hidden @ X53 @ ( k5_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 ) )
      | ( zip_tseitin_0 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X45 != X44 )
      | ~ ( zip_tseitin_0 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X44: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ~ ( zip_tseitin_0 @ X44 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X44 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X0 @ ( k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','15'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('17',plain,(
    ! [X32: $i,X34: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X32 ) @ X34 )
      | ~ ( r2_hidden @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
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

thf('20',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('21',plain,(
    ! [X66: $i,X68: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X66 @ X68 ) )
      = X68 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('22',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','24'])).

thf('26',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('28',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X40 ) @ ( k2_tarski @ X41 @ X42 ) )
      = ( k2_tarski @ ( k4_tarski @ X40 @ X41 ) @ ( k4_tarski @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ X0 ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ X0 ) @ ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ X0 ) ) )
        | ( ( k2_tarski @ sk_A @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ sk_A ) ) )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','31'])).

thf('33',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('34',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('37',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38 != X37 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X37 ) )
       != ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('38',plain,(
    ! [X37: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X37 ) )
     != ( k1_tarski @ X37 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('42',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('43',plain,(
    ! [X37: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X37 ) ) ),
    inference(demod,[status(thm)],['38','41','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','43'])).

thf('45',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('47',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('48',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X66 @ X67 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('50',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('52',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X40 ) @ ( k2_tarski @ X41 @ X42 ) )
      = ( k2_tarski @ ( k4_tarski @ X40 @ X41 ) @ ( k4_tarski @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ X0 ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
      = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','56'])).

thf('58',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('59',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('60',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('62',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X37: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X37 ) ) ),
    inference(demod,[status(thm)],['38','41','42'])).

thf('64',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','64'])).

thf('66',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('67',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['45','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iXazbxW9RO
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:10:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.21/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.61  % Solved by: fo/fo7.sh
% 0.21/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.61  % done 609 iterations in 0.167s
% 0.21/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.61  % SZS output start Refutation
% 0.21/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.61  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.61  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.61  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.61  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.61  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.21/0.61                                               $i > $i > $o).
% 0.21/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.61  thf(t70_enumset1, axiom,
% 0.21/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.61  thf('0', plain,
% 0.21/0.61      (![X5 : $i, X6 : $i]:
% 0.21/0.61         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.21/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.61  thf(t69_enumset1, axiom,
% 0.21/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.61  thf('1', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.21/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.61  thf('2', plain,
% 0.21/0.61      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.61      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.61  thf(t71_enumset1, axiom,
% 0.21/0.61    (![A:$i,B:$i,C:$i]:
% 0.21/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.61  thf('3', plain,
% 0.21/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.61         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.21/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.61  thf(t72_enumset1, axiom,
% 0.21/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.61     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.21/0.61  thf('4', plain,
% 0.21/0.61      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.61         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.21/0.61           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.21/0.61      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.61  thf(t73_enumset1, axiom,
% 0.21/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.61     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.21/0.61       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.21/0.61  thf('5', plain,
% 0.21/0.61      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.61         ((k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.21/0.61           = (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.21/0.61      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.21/0.61  thf(t74_enumset1, axiom,
% 0.21/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.61     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.61       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.21/0.61  thf('6', plain,
% 0.21/0.61      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.61         ((k5_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.21/0.61           = (k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24))),
% 0.21/0.61      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.21/0.61  thf(d5_enumset1, axiom,
% 0.21/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.61     ( ( ( H ) = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) <=>
% 0.21/0.61       ( ![I:$i]:
% 0.21/0.61         ( ( r2_hidden @ I @ H ) <=>
% 0.21/0.61           ( ~( ( ( I ) != ( G ) ) & ( ( I ) != ( F ) ) & ( ( I ) != ( E ) ) & 
% 0.21/0.61                ( ( I ) != ( D ) ) & ( ( I ) != ( C ) ) & ( ( I ) != ( B ) ) & 
% 0.21/0.61                ( ( I ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.61  thf(zf_stmt_0, type, zip_tseitin_0 :
% 0.21/0.61      $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.21/0.61  thf(zf_stmt_1, axiom,
% 0.21/0.61    (![I:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.61     ( ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.21/0.61       ( ( ( I ) != ( A ) ) & ( ( I ) != ( B ) ) & ( ( I ) != ( C ) ) & 
% 0.21/0.61         ( ( I ) != ( D ) ) & ( ( I ) != ( E ) ) & ( ( I ) != ( F ) ) & 
% 0.21/0.61         ( ( I ) != ( G ) ) ) ))).
% 0.21/0.61  thf(zf_stmt_2, axiom,
% 0.21/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.61     ( ( ( H ) = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) <=>
% 0.21/0.61       ( ![I:$i]:
% 0.21/0.61         ( ( r2_hidden @ I @ H ) <=>
% 0.21/0.61           ( ~( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.21/0.61  thf('7', plain,
% 0.21/0.61      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, 
% 0.21/0.61         X60 : $i, X61 : $i]:
% 0.21/0.61         ((zip_tseitin_0 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60)
% 0.21/0.61          | (r2_hidden @ X53 @ X61)
% 0.21/0.61          | ((X61) != (k5_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.61  thf('8', plain,
% 0.21/0.61      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, 
% 0.21/0.61         X60 : $i]:
% 0.21/0.61         ((r2_hidden @ X53 @ 
% 0.21/0.61           (k5_enumset1 @ X60 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54))
% 0.21/0.61          | (zip_tseitin_0 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60))),
% 0.21/0.61      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.61  thf('9', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.61         ((r2_hidden @ X6 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.61          | (zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5))),
% 0.21/0.61      inference('sup+', [status(thm)], ['6', '8'])).
% 0.21/0.61  thf('10', plain,
% 0.21/0.61      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, 
% 0.21/0.61         X51 : $i]:
% 0.21/0.61         (((X45) != (X44))
% 0.21/0.61          | ~ (zip_tseitin_0 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X44))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.61  thf('11', plain,
% 0.21/0.61      (![X44 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.21/0.61         ~ (zip_tseitin_0 @ X44 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X44)),
% 0.21/0.61      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.61  thf('12', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.61         (r2_hidden @ X0 @ (k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5))),
% 0.21/0.61      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.61  thf('13', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.61         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.61      inference('sup+', [status(thm)], ['5', '12'])).
% 0.21/0.61  thf('14', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.61         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.61      inference('sup+', [status(thm)], ['4', '13'])).
% 0.21/0.61  thf('15', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.61         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.61      inference('sup+', [status(thm)], ['3', '14'])).
% 0.21/0.61  thf('16', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.61      inference('sup+', [status(thm)], ['2', '15'])).
% 0.21/0.61  thf(l1_zfmisc_1, axiom,
% 0.21/0.61    (![A:$i,B:$i]:
% 0.21/0.61     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.61  thf('17', plain,
% 0.21/0.61      (![X32 : $i, X34 : $i]:
% 0.21/0.61         ((r1_tarski @ (k1_tarski @ X32) @ X34) | ~ (r2_hidden @ X32 @ X34))),
% 0.21/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.61  thf('18', plain,
% 0.21/0.61      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.61  thf('19', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.21/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.61  thf(t20_mcart_1, conjecture,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.21/0.61       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.21/0.61  thf(zf_stmt_3, negated_conjecture,
% 0.21/0.61    (~( ![A:$i]:
% 0.21/0.61        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.21/0.61          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.21/0.61    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.21/0.61  thf('20', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.61  thf(t7_mcart_1, axiom,
% 0.21/0.61    (![A:$i,B:$i]:
% 0.21/0.61     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.61       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.61  thf('21', plain,
% 0.21/0.61      (![X66 : $i, X68 : $i]: ((k2_mcart_1 @ (k4_tarski @ X66 @ X68)) = (X68))),
% 0.21/0.61      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.61  thf('22', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.21/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.61  thf('23', plain,
% 0.21/0.61      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.61  thf('24', plain,
% 0.21/0.61      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.61      inference('split', [status(esa)], ['23'])).
% 0.21/0.61  thf('25', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.61      inference('sup+', [status(thm)], ['22', '24'])).
% 0.21/0.61  thf('26', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.61  thf('27', plain,
% 0.21/0.61      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.21/0.61         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.61      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.61  thf(t36_zfmisc_1, axiom,
% 0.21/0.61    (![A:$i,B:$i,C:$i]:
% 0.21/0.61     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.44/0.61         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.44/0.61       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.44/0.61         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.44/0.61  thf('28', plain,
% 0.44/0.61      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.44/0.61         ((k2_zfmisc_1 @ (k1_tarski @ X40) @ (k2_tarski @ X41 @ X42))
% 0.44/0.61           = (k2_tarski @ (k4_tarski @ X40 @ X41) @ (k4_tarski @ X40 @ X42)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.44/0.61  thf('29', plain,
% 0.44/0.61      ((![X0 : $i]:
% 0.44/0.61          ((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_A @ X0))
% 0.44/0.61            = (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ X0))))
% 0.44/0.61         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.44/0.61  thf(t135_zfmisc_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.44/0.61         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.44/0.61       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.61  thf('30', plain,
% 0.44/0.61      (![X35 : $i, X36 : $i]:
% 0.44/0.61         (((X35) = (k1_xboole_0))
% 0.44/0.61          | ~ (r1_tarski @ X35 @ (k2_zfmisc_1 @ X36 @ X35)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.44/0.61  thf('31', plain,
% 0.44/0.61      ((![X0 : $i]:
% 0.44/0.61          (~ (r1_tarski @ (k2_tarski @ sk_A @ X0) @ 
% 0.44/0.61              (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ X0)))
% 0.44/0.61           | ((k2_tarski @ sk_A @ X0) = (k1_xboole_0))))
% 0.44/0.61         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.44/0.61  thf('32', plain,
% 0.44/0.61      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.44/0.61            (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ sk_A)))
% 0.44/0.61         | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))))
% 0.44/0.61         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['19', '31'])).
% 0.44/0.61  thf('33', plain,
% 0.44/0.61      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.44/0.61         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['25', '26'])).
% 0.44/0.61  thf('34', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.44/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.61  thf('35', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.44/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.61  thf('36', plain,
% 0.44/0.61      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.44/0.61         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.44/0.61         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.44/0.61  thf(t20_zfmisc_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.44/0.61         ( k1_tarski @ A ) ) <=>
% 0.44/0.61       ( ( A ) != ( B ) ) ))).
% 0.44/0.61  thf('37', plain,
% 0.44/0.61      (![X37 : $i, X38 : $i]:
% 0.44/0.61         (((X38) != (X37))
% 0.44/0.61          | ((k4_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X37))
% 0.44/0.61              != (k1_tarski @ X38)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.44/0.61  thf('38', plain,
% 0.44/0.61      (![X37 : $i]:
% 0.44/0.61         ((k4_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X37))
% 0.44/0.61           != (k1_tarski @ X37))),
% 0.44/0.61      inference('simplify', [status(thm)], ['37'])).
% 0.44/0.61  thf(idempotence_k3_xboole_0, axiom,
% 0.44/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.44/0.61  thf('39', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.44/0.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.44/0.61  thf(t100_xboole_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.61  thf('40', plain,
% 0.44/0.61      (![X1 : $i, X2 : $i]:
% 0.44/0.61         ((k4_xboole_0 @ X1 @ X2)
% 0.44/0.61           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.61  thf('41', plain,
% 0.44/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['39', '40'])).
% 0.44/0.61  thf(t92_xboole_1, axiom,
% 0.44/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.44/0.61  thf('42', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.44/0.61      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.44/0.61  thf('43', plain, (![X37 : $i]: ((k1_xboole_0) != (k1_tarski @ X37))),
% 0.44/0.61      inference('demod', [status(thm)], ['38', '41', '42'])).
% 0.44/0.61  thf('44', plain,
% 0.44/0.61      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.44/0.61         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('clc', [status(thm)], ['36', '43'])).
% 0.44/0.61  thf('45', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['18', '44'])).
% 0.44/0.61  thf('46', plain,
% 0.44/0.61      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.44/0.61  thf('47', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.44/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.61  thf('48', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.61  thf('49', plain,
% 0.44/0.61      (![X66 : $i, X67 : $i]: ((k1_mcart_1 @ (k4_tarski @ X66 @ X67)) = (X66))),
% 0.44/0.61      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.44/0.61  thf('50', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.44/0.61      inference('sup+', [status(thm)], ['48', '49'])).
% 0.44/0.61  thf('51', plain,
% 0.44/0.61      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('split', [status(esa)], ['23'])).
% 0.44/0.61  thf('52', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['50', '51'])).
% 0.44/0.61  thf('53', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.61  thf('54', plain,
% 0.44/0.61      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.44/0.61         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['52', '53'])).
% 0.44/0.61  thf('55', plain,
% 0.44/0.61      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.44/0.61         ((k2_zfmisc_1 @ (k1_tarski @ X40) @ (k2_tarski @ X41 @ X42))
% 0.44/0.61           = (k2_tarski @ (k4_tarski @ X40 @ X41) @ (k4_tarski @ X40 @ X42)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.44/0.61  thf('56', plain,
% 0.44/0.61      ((![X0 : $i]:
% 0.44/0.61          ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ X0))
% 0.44/0.61            = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ X0))))
% 0.44/0.61         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['54', '55'])).
% 0.44/0.61  thf('57', plain,
% 0.44/0.61      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.44/0.61          = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ sk_C))))
% 0.44/0.61         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['47', '56'])).
% 0.44/0.61  thf('58', plain,
% 0.44/0.61      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.44/0.61         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['52', '53'])).
% 0.44/0.61  thf('59', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.44/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.61  thf('60', plain,
% 0.44/0.61      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.44/0.61          = (k1_tarski @ sk_A)))
% 0.44/0.61         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.44/0.61  thf('61', plain,
% 0.44/0.61      (![X35 : $i, X36 : $i]:
% 0.44/0.61         (((X35) = (k1_xboole_0))
% 0.44/0.61          | ~ (r1_tarski @ X35 @ (k2_zfmisc_1 @ X35 @ X36)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.44/0.61  thf('62', plain,
% 0.44/0.61      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.44/0.61         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.44/0.61         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['60', '61'])).
% 0.44/0.61  thf('63', plain, (![X37 : $i]: ((k1_xboole_0) != (k1_tarski @ X37))),
% 0.44/0.61      inference('demod', [status(thm)], ['38', '41', '42'])).
% 0.44/0.61  thf('64', plain,
% 0.44/0.61      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.44/0.61         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.44/0.61      inference('clc', [status(thm)], ['62', '63'])).
% 0.44/0.61  thf('65', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['46', '64'])).
% 0.44/0.61  thf('66', plain,
% 0.44/0.61      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.44/0.61      inference('split', [status(esa)], ['23'])).
% 0.44/0.61  thf('67', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.44/0.61      inference('sat_resolution*', [status(thm)], ['65', '66'])).
% 0.44/0.61  thf('68', plain, ($false),
% 0.44/0.61      inference('simpl_trail', [status(thm)], ['45', '67'])).
% 0.44/0.61  
% 0.44/0.61  % SZS output end Refutation
% 0.44/0.61  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
