%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.APzK2wuTsK

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:09 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 233 expanded)
%              Number of leaves         :   44 (  87 expanded)
%              Depth                    :   13
%              Number of atoms          : 1005 (2133 expanded)
%              Number of equality atoms :  126 ( 294 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k5_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k6_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(d6_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( ( J != H )
              & ( J != G )
              & ( J != F )
              & ( J != E )
              & ( J != D )
              & ( J != C )
              & ( J != B )
              & ( J != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [J: $i,H: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( J != A )
        & ( J != B )
        & ( J != C )
        & ( J != D )
        & ( J != E )
        & ( J != F )
        & ( J != G )
        & ( J != H ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ( zip_tseitin_0 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 )
      | ( r2_hidden @ X55 @ X64 )
      | ( X64
       != ( k6_enumset1 @ X63 @ X62 @ X61 @ X60 @ X59 @ X58 @ X57 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( r2_hidden @ X55 @ ( k6_enumset1 @ X63 @ X62 @ X61 @ X60 @ X59 @ X58 @ X57 @ X56 ) )
      | ( zip_tseitin_0 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X46 != X45 )
      | ~ ( zip_tseitin_0 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    ! [X45: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ~ ( zip_tseitin_0 @ X45 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X45 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','17'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X31 ) @ X33 )
      | ~ ( r2_hidden @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
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

thf('22',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('23',plain,(
    ! [X69: $i,X71: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X69 @ X71 ) )
      = X71 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('24',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('28',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('30',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X41 ) @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_tarski @ ( k4_tarski @ X41 @ X42 ) @ ( k4_tarski @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ X0 ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_B @ sk_A ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','31'])).

thf('33',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('34',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('36',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34 = k1_xboole_0 )
      | ~ ( r1_tarski @ X34 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('37',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('38',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39 != X38 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X39 ) @ ( k1_tarski @ X38 ) )
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('39',plain,(
    ! [X38: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X38 ) )
     != ( k1_tarski @ X38 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('41',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X36 ) @ ( k2_tarski @ X36 @ X37 ) )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X67: $i,X68: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X67 @ X68 ) )
      = ( k3_xboole_0 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('51',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X38: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X38 ) ) ),
    inference(demod,[status(thm)],['39','52'])).

thf('54',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','53'])).

thf('55',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('57',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,(
    ! [X69: $i,X70: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X69 @ X70 ) )
      = X69 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('59',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('61',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('63',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('65',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X41 ) @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_tarski @ ( k4_tarski @ X41 @ X42 ) @ ( k4_tarski @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ X0 ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34 = k1_xboole_0 )
      | ~ ( r1_tarski @ X34 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ X0 ) ) )
        | ( ( k1_tarski @ sk_A )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('71',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X38: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X38 ) ) ),
    inference(demod,[status(thm)],['39','52'])).

thf('73',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','73'])).

thf('75',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('76',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['55','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.APzK2wuTsK
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:09:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.53/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.73  % Solved by: fo/fo7.sh
% 0.53/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.73  % done 883 iterations in 0.277s
% 0.53/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.73  % SZS output start Refutation
% 0.53/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.53/0.73  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.53/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.53/0.73                                               $i > $i > $i > $o).
% 0.53/0.73  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.53/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.53/0.73  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.53/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.73  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.53/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.73  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.53/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.73  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.53/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.73  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.53/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.73  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.53/0.73                                           $i > $i).
% 0.53/0.73  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.53/0.73  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.53/0.73  thf(t70_enumset1, axiom,
% 0.53/0.73    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.53/0.73  thf('0', plain,
% 0.53/0.73      (![X4 : $i, X5 : $i]:
% 0.53/0.73         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 0.53/0.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.53/0.73  thf(t69_enumset1, axiom,
% 0.53/0.73    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.53/0.73  thf('1', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.53/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.73  thf('2', plain,
% 0.53/0.73      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['0', '1'])).
% 0.53/0.73  thf(t71_enumset1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.53/0.73  thf('3', plain,
% 0.53/0.73      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.53/0.73         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.53/0.73      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.53/0.73  thf(t72_enumset1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.73     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.53/0.73  thf('4', plain,
% 0.53/0.73      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.53/0.73         ((k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12)
% 0.53/0.73           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 0.53/0.73      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.53/0.73  thf(t73_enumset1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.53/0.73     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.53/0.73       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.53/0.73  thf('5', plain,
% 0.53/0.73      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.53/0.73         ((k4_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.53/0.73           = (k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17))),
% 0.53/0.73      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.53/0.73  thf(t74_enumset1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.53/0.73     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.53/0.73       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.53/0.73  thf('6', plain,
% 0.53/0.73      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.53/0.73         ((k5_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.53/0.73           = (k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23))),
% 0.53/0.73      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.53/0.73  thf(t75_enumset1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.53/0.73     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.53/0.73       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.53/0.73  thf('7', plain,
% 0.53/0.73      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.53/0.73         ((k6_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.53/0.73           = (k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.53/0.73  thf(d6_enumset1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.53/0.73     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.53/0.73       ( ![J:$i]:
% 0.53/0.73         ( ( r2_hidden @ J @ I ) <=>
% 0.53/0.73           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.53/0.73                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.53/0.73                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.53/0.73  thf(zf_stmt_0, type, zip_tseitin_0 :
% 0.53/0.73      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.53/0.73  thf(zf_stmt_1, axiom,
% 0.53/0.73    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.53/0.73     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.53/0.73       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.53/0.73         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.53/0.73         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.53/0.73  thf(zf_stmt_2, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.53/0.73     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.53/0.73       ( ![J:$i]:
% 0.53/0.73         ( ( r2_hidden @ J @ I ) <=>
% 0.53/0.73           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.53/0.73  thf('8', plain,
% 0.53/0.73      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i, 
% 0.53/0.73         X62 : $i, X63 : $i, X64 : $i]:
% 0.53/0.73         ((zip_tseitin_0 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63)
% 0.53/0.73          | (r2_hidden @ X55 @ X64)
% 0.53/0.73          | ((X64)
% 0.53/0.73              != (k6_enumset1 @ X63 @ X62 @ X61 @ X60 @ X59 @ X58 @ X57 @ X56)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.53/0.73  thf('9', plain,
% 0.53/0.73      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i, 
% 0.53/0.73         X62 : $i, X63 : $i]:
% 0.53/0.73         ((r2_hidden @ X55 @ 
% 0.53/0.73           (k6_enumset1 @ X63 @ X62 @ X61 @ X60 @ X59 @ X58 @ X57 @ X56))
% 0.53/0.73          | (zip_tseitin_0 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 @ 
% 0.53/0.73             X63))),
% 0.53/0.73      inference('simplify', [status(thm)], ['8'])).
% 0.53/0.73  thf('10', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.53/0.73         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.53/0.73          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.53/0.73      inference('sup+', [status(thm)], ['7', '9'])).
% 0.53/0.73  thf('11', plain,
% 0.53/0.73      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, 
% 0.53/0.73         X52 : $i, X53 : $i]:
% 0.53/0.73         (((X46) != (X45))
% 0.53/0.73          | ~ (zip_tseitin_0 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ 
% 0.53/0.73               X45))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.53/0.73  thf('12', plain,
% 0.53/0.73      (![X45 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, 
% 0.53/0.73         X53 : $i]:
% 0.53/0.73         ~ (zip_tseitin_0 @ X45 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X45)),
% 0.53/0.73      inference('simplify', [status(thm)], ['11'])).
% 0.53/0.73  thf('13', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.73         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.53/0.73      inference('sup-', [status(thm)], ['10', '12'])).
% 0.53/0.73  thf('14', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.53/0.73         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['6', '13'])).
% 0.53/0.73  thf('15', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.53/0.73         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['5', '14'])).
% 0.53/0.73  thf('16', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.73         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['4', '15'])).
% 0.53/0.73  thf('17', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['3', '16'])).
% 0.53/0.73  thf('18', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['2', '17'])).
% 0.53/0.73  thf(l1_zfmisc_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.53/0.73  thf('19', plain,
% 0.53/0.73      (![X31 : $i, X33 : $i]:
% 0.53/0.73         ((r1_tarski @ (k1_tarski @ X31) @ X33) | ~ (r2_hidden @ X31 @ X33))),
% 0.53/0.73      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.53/0.73  thf('20', plain,
% 0.53/0.73      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.53/0.73  thf('21', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.53/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.73  thf(t20_mcart_1, conjecture,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.53/0.73       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.53/0.73  thf(zf_stmt_3, negated_conjecture,
% 0.53/0.73    (~( ![A:$i]:
% 0.53/0.73        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.53/0.73          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.53/0.73    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.53/0.73  thf('22', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.53/0.73  thf(t7_mcart_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.53/0.73       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.53/0.73  thf('23', plain,
% 0.53/0.73      (![X69 : $i, X71 : $i]: ((k2_mcart_1 @ (k4_tarski @ X69 @ X71)) = (X71))),
% 0.53/0.73      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.53/0.73  thf('24', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.53/0.73      inference('sup+', [status(thm)], ['22', '23'])).
% 0.53/0.73  thf('25', plain,
% 0.53/0.73      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.53/0.73  thf('26', plain,
% 0.53/0.73      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('split', [status(esa)], ['25'])).
% 0.53/0.73  thf('27', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['24', '26'])).
% 0.53/0.73  thf('28', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.53/0.73  thf('29', plain,
% 0.53/0.73      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.53/0.73         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.73  thf(t36_zfmisc_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.53/0.73         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.53/0.73       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.53/0.73         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.53/0.73  thf('30', plain,
% 0.53/0.73      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.53/0.73         ((k2_zfmisc_1 @ (k1_tarski @ X41) @ (k2_tarski @ X42 @ X43))
% 0.53/0.73           = (k2_tarski @ (k4_tarski @ X41 @ X42) @ (k4_tarski @ X41 @ X43)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.53/0.73  thf('31', plain,
% 0.53/0.73      ((![X0 : $i]:
% 0.53/0.73          ((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_A @ X0))
% 0.53/0.73            = (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ X0))))
% 0.53/0.73         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['29', '30'])).
% 0.53/0.73  thf('32', plain,
% 0.53/0.73      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.53/0.73          = (k2_tarski @ sk_A @ (k4_tarski @ sk_B @ sk_A))))
% 0.53/0.73         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['21', '31'])).
% 0.53/0.73  thf('33', plain,
% 0.53/0.73      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.53/0.73         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.73  thf('34', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.53/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.73  thf('35', plain,
% 0.53/0.73      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.53/0.73          = (k1_tarski @ sk_A)))
% 0.53/0.73         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.53/0.73  thf(t135_zfmisc_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.53/0.73         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.53/0.73       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.53/0.73  thf('36', plain,
% 0.53/0.73      (![X34 : $i, X35 : $i]:
% 0.53/0.73         (((X34) = (k1_xboole_0))
% 0.53/0.73          | ~ (r1_tarski @ X34 @ (k2_zfmisc_1 @ X35 @ X34)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.53/0.73  thf('37', plain,
% 0.53/0.73      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.53/0.73         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.53/0.73         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['35', '36'])).
% 0.53/0.73  thf(t20_zfmisc_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.53/0.73         ( k1_tarski @ A ) ) <=>
% 0.53/0.73       ( ( A ) != ( B ) ) ))).
% 0.53/0.73  thf('38', plain,
% 0.53/0.73      (![X38 : $i, X39 : $i]:
% 0.53/0.73         (((X39) != (X38))
% 0.53/0.73          | ((k4_xboole_0 @ (k1_tarski @ X39) @ (k1_tarski @ X38))
% 0.53/0.73              != (k1_tarski @ X39)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.53/0.73  thf('39', plain,
% 0.53/0.73      (![X38 : $i]:
% 0.53/0.73         ((k4_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X38))
% 0.53/0.73           != (k1_tarski @ X38))),
% 0.53/0.73      inference('simplify', [status(thm)], ['38'])).
% 0.53/0.73  thf('40', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.53/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.73  thf(t19_zfmisc_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.53/0.73       ( k1_tarski @ A ) ))).
% 0.53/0.73  thf('41', plain,
% 0.53/0.73      (![X36 : $i, X37 : $i]:
% 0.53/0.73         ((k3_xboole_0 @ (k1_tarski @ X36) @ (k2_tarski @ X36 @ X37))
% 0.53/0.73           = (k1_tarski @ X36))),
% 0.53/0.73      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.53/0.73  thf('42', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.53/0.73           = (k1_tarski @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['40', '41'])).
% 0.53/0.73  thf('43', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.53/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.73  thf(t12_setfam_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.73  thf('44', plain,
% 0.53/0.73      (![X67 : $i, X68 : $i]:
% 0.53/0.73         ((k1_setfam_1 @ (k2_tarski @ X67 @ X68)) = (k3_xboole_0 @ X67 @ X68))),
% 0.53/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.53/0.73  thf('45', plain,
% 0.53/0.73      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['43', '44'])).
% 0.53/0.73  thf('46', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k1_setfam_1 @ (k1_tarski @ (k1_tarski @ X0))) = (k1_tarski @ X0))),
% 0.53/0.73      inference('demod', [status(thm)], ['42', '45'])).
% 0.53/0.73  thf('47', plain,
% 0.53/0.73      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['43', '44'])).
% 0.53/0.73  thf(t100_xboole_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.73  thf('48', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k4_xboole_0 @ X0 @ X1)
% 0.53/0.73           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.73  thf('49', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k4_xboole_0 @ X0 @ X0)
% 0.53/0.73           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['47', '48'])).
% 0.53/0.73  thf('50', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.53/0.73           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['46', '49'])).
% 0.53/0.73  thf(t92_xboole_1, axiom,
% 0.53/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.53/0.73  thf('51', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ X2) = (k1_xboole_0))),
% 0.53/0.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.73  thf('52', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.53/0.73      inference('demod', [status(thm)], ['50', '51'])).
% 0.53/0.73  thf('53', plain, (![X38 : $i]: ((k1_xboole_0) != (k1_tarski @ X38))),
% 0.53/0.73      inference('demod', [status(thm)], ['39', '52'])).
% 0.53/0.73  thf('54', plain,
% 0.53/0.73      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.53/0.73         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('clc', [status(thm)], ['37', '53'])).
% 0.53/0.73  thf('55', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['20', '54'])).
% 0.53/0.73  thf('56', plain,
% 0.53/0.73      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.53/0.73  thf('57', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.53/0.73  thf('58', plain,
% 0.53/0.73      (![X69 : $i, X70 : $i]: ((k1_mcart_1 @ (k4_tarski @ X69 @ X70)) = (X69))),
% 0.53/0.73      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.53/0.73  thf('59', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.53/0.73      inference('sup+', [status(thm)], ['57', '58'])).
% 0.53/0.73  thf('60', plain,
% 0.53/0.73      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('split', [status(esa)], ['25'])).
% 0.53/0.73  thf('61', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['59', '60'])).
% 0.53/0.73  thf('62', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.53/0.73  thf('63', plain,
% 0.53/0.73      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.53/0.73         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['61', '62'])).
% 0.53/0.73  thf('64', plain,
% 0.53/0.73      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.53/0.73         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['61', '62'])).
% 0.53/0.73  thf('65', plain,
% 0.53/0.73      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.53/0.73         ((k2_zfmisc_1 @ (k1_tarski @ X41) @ (k2_tarski @ X42 @ X43))
% 0.53/0.73           = (k2_tarski @ (k4_tarski @ X41 @ X42) @ (k4_tarski @ X41 @ X43)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.53/0.73  thf('66', plain,
% 0.53/0.73      ((![X0 : $i]:
% 0.53/0.73          ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ X0))
% 0.53/0.73            = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ X0))))
% 0.53/0.73         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['64', '65'])).
% 0.53/0.73  thf('67', plain,
% 0.53/0.73      (![X34 : $i, X35 : $i]:
% 0.53/0.73         (((X34) = (k1_xboole_0))
% 0.53/0.73          | ~ (r1_tarski @ X34 @ (k2_zfmisc_1 @ X34 @ X35)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.53/0.73  thf('68', plain,
% 0.53/0.73      ((![X0 : $i]:
% 0.53/0.73          (~ (r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.53/0.73              (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ X0)))
% 0.53/0.73           | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.53/0.73         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['66', '67'])).
% 0.53/0.73  thf('69', plain,
% 0.53/0.73      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_A))
% 0.53/0.73         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.53/0.73         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['63', '68'])).
% 0.53/0.73  thf('70', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.53/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.73  thf('71', plain,
% 0.53/0.73      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.53/0.73         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.53/0.73         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('demod', [status(thm)], ['69', '70'])).
% 0.53/0.73  thf('72', plain, (![X38 : $i]: ((k1_xboole_0) != (k1_tarski @ X38))),
% 0.53/0.73      inference('demod', [status(thm)], ['39', '52'])).
% 0.53/0.73  thf('73', plain,
% 0.53/0.73      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.53/0.73         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.53/0.73      inference('clc', [status(thm)], ['71', '72'])).
% 0.53/0.73  thf('74', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['56', '73'])).
% 0.53/0.73  thf('75', plain,
% 0.53/0.73      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.53/0.73      inference('split', [status(esa)], ['25'])).
% 0.53/0.73  thf('76', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.53/0.73      inference('sat_resolution*', [status(thm)], ['74', '75'])).
% 0.53/0.73  thf('77', plain, ($false),
% 0.53/0.73      inference('simpl_trail', [status(thm)], ['55', '76'])).
% 0.53/0.73  
% 0.53/0.73  % SZS output end Refutation
% 0.53/0.73  
% 0.53/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
