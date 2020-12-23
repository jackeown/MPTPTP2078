%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pHnsRkPo2y

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:09 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 251 expanded)
%              Number of leaves         :   44 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          : 1000 (2216 expanded)
%              Number of equality atoms :  129 ( 320 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
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
    ! [X59: $i,X60: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i,X66: $i,X67: $i] :
      ( ( zip_tseitin_0 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 )
      | ( r2_hidden @ X59 @ X67 )
      | ( X67
       != ( k5_enumset1 @ X66 @ X65 @ X64 @ X63 @ X62 @ X61 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ( r2_hidden @ X59 @ ( k5_enumset1 @ X66 @ X65 @ X64 @ X63 @ X62 @ X61 @ X60 ) )
      | ( zip_tseitin_0 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( X51 != X50 )
      | ~ ( zip_tseitin_0 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X50: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ~ ( zip_tseitin_0 @ X50 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X50 ) ),
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
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

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

thf('19',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('20',plain,(
    ! [X72: $i,X73: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X72 @ X73 ) )
      = X72 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('25',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('28',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X46 ) @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_tarski @ ( k4_tarski @ X46 @ X47 ) @ ( k4_tarski @ X46 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ X0 @ sk_C ) )
        = ( k2_tarski @ ( k4_tarski @ sk_A @ X0 ) @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X39: $i,X40: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( r1_tarski @ X39 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ ( k4_tarski @ sk_A @ X0 ) @ sk_A ) )
        | ( ( k1_tarski @ sk_A )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('32',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X44 != X43 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X43 ) )
       != ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('33',plain,(
    ! [X43: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X43 ) )
     != ( k1_tarski @ X43 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('35',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X41 ) @ ( k2_tarski @ X41 @ X42 ) )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X70: $i,X71: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X70 @ X71 ) )
      = ( k3_xboole_0 @ X70 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X43: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X43 ) ) ),
    inference(demod,[status(thm)],['33','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ ( k4_tarski @ sk_A @ X0 ) @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['31','51'])).

thf('53',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','52'])).

thf('54',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( $false
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('58',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('59',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,(
    ! [X72: $i,X74: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X72 @ X74 ) )
      = X74 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('61',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('63',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('65',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X46 ) @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_tarski @ ( k4_tarski @ X46 @ X47 ) @ ( k4_tarski @ X46 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ X0 ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X39: $i,X40: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( r1_tarski @ X39 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ X0 ) @ ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ X0 ) ) )
        | ( ( k2_tarski @ sk_A @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ ( k2_tarski @ sk_A @ sk_A ) )
      | ( ( k2_tarski @ sk_A @ sk_C )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('72',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('73',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('74',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('75',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('76',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72','73','74','75'])).

thf('77',plain,(
    ! [X43: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X43 ) ) ),
    inference(demod,[status(thm)],['33','50'])).

thf('78',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','78'])).

thf('80',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('81',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['56','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pHnsRkPo2y
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 780 iterations in 0.212s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.45/0.67                                               $i > $i > $o).
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.67  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.45/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.67  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.67  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(t70_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (![X7 : $i, X8 : $i]:
% 0.45/0.67         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.45/0.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.67  thf(t69_enumset1, axiom,
% 0.45/0.67    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.67  thf('1', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['0', '1'])).
% 0.45/0.67  thf(t71_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.67         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.45/0.67      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.67  thf(t72_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.67         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 0.45/0.67           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.45/0.67  thf(t73_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.67     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.45/0.67       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.67         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.45/0.67           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.45/0.67      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.45/0.67  thf(t74_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.67     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.45/0.67       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.67         ((k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.45/0.67           = (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 0.45/0.67      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.45/0.67  thf(d5_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.45/0.67     ( ( ( H ) = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) <=>
% 0.45/0.67       ( ![I:$i]:
% 0.45/0.67         ( ( r2_hidden @ I @ H ) <=>
% 0.45/0.67           ( ~( ( ( I ) != ( G ) ) & ( ( I ) != ( F ) ) & ( ( I ) != ( E ) ) & 
% 0.45/0.67                ( ( I ) != ( D ) ) & ( ( I ) != ( C ) ) & ( ( I ) != ( B ) ) & 
% 0.45/0.67                ( ( I ) != ( A ) ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, type, zip_tseitin_0 :
% 0.45/0.67      $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.45/0.67  thf(zf_stmt_1, axiom,
% 0.45/0.67    (![I:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.45/0.67     ( ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.45/0.67       ( ( ( I ) != ( A ) ) & ( ( I ) != ( B ) ) & ( ( I ) != ( C ) ) & 
% 0.45/0.67         ( ( I ) != ( D ) ) & ( ( I ) != ( E ) ) & ( ( I ) != ( F ) ) & 
% 0.45/0.67         ( ( I ) != ( G ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_2, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.45/0.67     ( ( ( H ) = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) <=>
% 0.45/0.67       ( ![I:$i]:
% 0.45/0.67         ( ( r2_hidden @ I @ H ) <=>
% 0.45/0.67           ( ~( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i, 
% 0.45/0.67         X66 : $i, X67 : $i]:
% 0.45/0.67         ((zip_tseitin_0 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66)
% 0.45/0.67          | (r2_hidden @ X59 @ X67)
% 0.45/0.67          | ((X67) != (k5_enumset1 @ X66 @ X65 @ X64 @ X63 @ X62 @ X61 @ X60)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i, 
% 0.45/0.67         X66 : $i]:
% 0.45/0.67         ((r2_hidden @ X59 @ 
% 0.45/0.67           (k5_enumset1 @ X66 @ X65 @ X64 @ X63 @ X62 @ X61 @ X60))
% 0.45/0.67          | (zip_tseitin_0 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66))),
% 0.45/0.67      inference('simplify', [status(thm)], ['7'])).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.67         ((r2_hidden @ X6 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.45/0.67          | (zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5))),
% 0.45/0.67      inference('sup+', [status(thm)], ['6', '8'])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, 
% 0.45/0.67         X57 : $i]:
% 0.45/0.67         (((X51) != (X50))
% 0.45/0.67          | ~ (zip_tseitin_0 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X50))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X50 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.45/0.67         ~ (zip_tseitin_0 @ X50 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X50)),
% 0.45/0.67      inference('simplify', [status(thm)], ['10'])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.67         (r2_hidden @ X0 @ (k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5))),
% 0.45/0.67      inference('sup-', [status(thm)], ['9', '11'])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.67         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['5', '12'])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.67         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['4', '13'])).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['3', '14'])).
% 0.45/0.67  thf('16', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['2', '15'])).
% 0.45/0.67  thf(l1_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      (![X34 : $i, X36 : $i]:
% 0.45/0.67         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 0.45/0.67      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.67  thf(t20_mcart_1, conjecture,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.45/0.67       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_3, negated_conjecture,
% 0.45/0.67    (~( ![A:$i]:
% 0.45/0.67        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.45/0.67          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.45/0.67  thf('19', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.67  thf(t7_mcart_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.45/0.67       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X72 : $i, X73 : $i]: ((k1_mcart_1 @ (k4_tarski @ X72 @ X73)) = (X72))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.45/0.67  thf('21', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['19', '20'])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('split', [status(esa)], ['22'])).
% 0.45/0.67  thf('24', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['21', '23'])).
% 0.45/0.67  thf('25', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.45/0.67         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['24', '25'])).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.45/0.67         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['24', '25'])).
% 0.45/0.67  thf(t36_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.45/0.67         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.45/0.67       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.45/0.67         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.45/0.67         ((k2_zfmisc_1 @ (k1_tarski @ X46) @ (k2_tarski @ X47 @ X48))
% 0.45/0.67           = (k2_tarski @ (k4_tarski @ X46 @ X47) @ (k4_tarski @ X46 @ X48)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ X0 @ sk_C))
% 0.45/0.67            = (k2_tarski @ (k4_tarski @ sk_A @ X0) @ sk_A)))
% 0.45/0.67         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['27', '28'])).
% 0.45/0.67  thf(t135_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.45/0.67         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.45/0.67       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      (![X39 : $i, X40 : $i]:
% 0.45/0.67         (((X39) = (k1_xboole_0))
% 0.45/0.67          | ~ (r1_tarski @ X39 @ (k2_zfmisc_1 @ X39 @ X40)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          (~ (r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.45/0.67              (k2_tarski @ (k4_tarski @ sk_A @ X0) @ sk_A))
% 0.45/0.67           | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.45/0.67         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.67  thf(t20_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.45/0.67         ( k1_tarski @ A ) ) <=>
% 0.45/0.67       ( ( A ) != ( B ) ) ))).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      (![X43 : $i, X44 : $i]:
% 0.45/0.67         (((X44) != (X43))
% 0.45/0.67          | ((k4_xboole_0 @ (k1_tarski @ X44) @ (k1_tarski @ X43))
% 0.45/0.67              != (k1_tarski @ X44)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (![X43 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X43))
% 0.45/0.67           != (k1_tarski @ X43))),
% 0.45/0.67      inference('simplify', [status(thm)], ['32'])).
% 0.45/0.67  thf('34', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf(t19_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.45/0.67       ( k1_tarski @ A ) ))).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X41 : $i, X42 : $i]:
% 0.45/0.67         ((k3_xboole_0 @ (k1_tarski @ X41) @ (k2_tarski @ X41 @ X42))
% 0.45/0.67           = (k1_tarski @ X41))),
% 0.45/0.67      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.45/0.67           = (k1_tarski @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['34', '35'])).
% 0.45/0.67  thf('37', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf(t12_setfam_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      (![X70 : $i, X71 : $i]:
% 0.45/0.67         ((k1_setfam_1 @ (k2_tarski @ X70 @ X71)) = (k3_xboole_0 @ X70 @ X71))),
% 0.45/0.67      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['37', '38'])).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k1_setfam_1 @ (k1_tarski @ (k1_tarski @ X0))) = (k1_tarski @ X0))),
% 0.45/0.67      inference('demod', [status(thm)], ['36', '39'])).
% 0.45/0.67  thf('41', plain,
% 0.45/0.67      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['37', '38'])).
% 0.45/0.67  thf(t100_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.67  thf('42', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.67           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.67  thf('43', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X0 @ X0)
% 0.45/0.67           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['41', '42'])).
% 0.45/0.67  thf('44', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.45/0.67           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['40', '43'])).
% 0.45/0.67  thf(t21_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.45/0.67  thf('45', plain,
% 0.45/0.67      (![X2 : $i, X3 : $i]:
% 0.45/0.67         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.45/0.67  thf('46', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.67           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.67  thf('47', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.45/0.67           = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['45', '46'])).
% 0.45/0.67  thf(t46_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.45/0.67  thf('48', plain,
% 0.45/0.67      (![X4 : $i, X5 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (k1_xboole_0))),
% 0.45/0.67      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.45/0.67  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['47', '48'])).
% 0.45/0.67  thf('50', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['44', '49'])).
% 0.45/0.67  thf('51', plain, (![X43 : $i]: ((k1_xboole_0) != (k1_tarski @ X43))),
% 0.45/0.67      inference('demod', [status(thm)], ['33', '50'])).
% 0.45/0.67  thf('52', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          ~ (r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.45/0.67             (k2_tarski @ (k4_tarski @ sk_A @ X0) @ sk_A)))
% 0.45/0.67         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('clc', [status(thm)], ['31', '51'])).
% 0.45/0.67  thf('53', plain,
% 0.45/0.67      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_A)))
% 0.45/0.67         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['26', '52'])).
% 0.45/0.67  thf('54', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf('55', plain,
% 0.45/0.67      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.45/0.67         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('demod', [status(thm)], ['53', '54'])).
% 0.45/0.67  thf('56', plain, (($false) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['18', '55'])).
% 0.45/0.67  thf('57', plain,
% 0.45/0.67      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.67  thf('58', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.67  thf('59', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.67  thf('60', plain,
% 0.45/0.67      (![X72 : $i, X74 : $i]: ((k2_mcart_1 @ (k4_tarski @ X72 @ X74)) = (X74))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.45/0.67  thf('61', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.45/0.67      inference('sup+', [status(thm)], ['59', '60'])).
% 0.45/0.67  thf('62', plain,
% 0.45/0.67      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('split', [status(esa)], ['22'])).
% 0.45/0.67  thf('63', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['61', '62'])).
% 0.45/0.67  thf('64', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.67  thf('65', plain,
% 0.45/0.67      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.45/0.67         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['63', '64'])).
% 0.45/0.67  thf('66', plain,
% 0.45/0.67      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.45/0.67         ((k2_zfmisc_1 @ (k1_tarski @ X46) @ (k2_tarski @ X47 @ X48))
% 0.45/0.67           = (k2_tarski @ (k4_tarski @ X46 @ X47) @ (k4_tarski @ X46 @ X48)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.45/0.67  thf('67', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          ((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_A @ X0))
% 0.45/0.67            = (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ X0))))
% 0.45/0.67         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['65', '66'])).
% 0.45/0.67  thf('68', plain,
% 0.45/0.67      (![X39 : $i, X40 : $i]:
% 0.45/0.67         (((X39) = (k1_xboole_0))
% 0.45/0.67          | ~ (r1_tarski @ X39 @ (k2_zfmisc_1 @ X40 @ X39)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.45/0.67  thf('69', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          (~ (r1_tarski @ (k2_tarski @ sk_A @ X0) @ 
% 0.45/0.67              (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ X0)))
% 0.45/0.67           | ((k2_tarski @ sk_A @ X0) = (k1_xboole_0))))
% 0.45/0.67         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['67', '68'])).
% 0.45/0.67  thf('70', plain,
% 0.45/0.67      (((~ (r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ (k2_tarski @ sk_A @ sk_A))
% 0.45/0.67         | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))))
% 0.45/0.67         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['58', '69'])).
% 0.45/0.67  thf('71', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['61', '62'])).
% 0.45/0.67  thf('72', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf('73', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf('74', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['61', '62'])).
% 0.45/0.67  thf('75', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf('76', plain,
% 0.45/0.67      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.45/0.67         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.45/0.67         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('demod', [status(thm)], ['70', '71', '72', '73', '74', '75'])).
% 0.45/0.67  thf('77', plain, (![X43 : $i]: ((k1_xboole_0) != (k1_tarski @ X43))),
% 0.45/0.67      inference('demod', [status(thm)], ['33', '50'])).
% 0.45/0.67  thf('78', plain,
% 0.45/0.67      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.45/0.67         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.45/0.67      inference('clc', [status(thm)], ['76', '77'])).
% 0.45/0.67  thf('79', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['57', '78'])).
% 0.45/0.67  thf('80', plain,
% 0.45/0.67      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.45/0.67      inference('split', [status(esa)], ['22'])).
% 0.45/0.67  thf('81', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.45/0.67      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 0.45/0.67  thf('82', plain, ($false),
% 0.45/0.67      inference('simpl_trail', [status(thm)], ['56', '81'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
