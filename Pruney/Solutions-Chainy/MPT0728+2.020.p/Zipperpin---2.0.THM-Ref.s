%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qPJlCTpXdx

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:40 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 359 expanded)
%              Number of leaves         :   28 ( 110 expanded)
%              Depth                    :   23
%              Number of atoms          : 1248 (5265 expanded)
%              Number of equality atoms :   96 ( 400 expanded)
%              Maximal formula depth    :   23 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t10_ordinal1,conjecture,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t10_ordinal1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 )
      | ( X37 = X38 )
      | ( X37 = X39 )
      | ( X37 = X40 )
      | ( X37 = X41 )
      | ( X37 = X42 )
      | ( X37 = X43 )
      | ( X37 = X44 )
      | ( X37 = X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('4',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X56 @ X55 )
      | ~ ( zip_tseitin_0 @ X56 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 )
      | ( X55
       != ( k6_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X56: $i] :
      ( ~ ( zip_tseitin_0 @ X56 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 )
      | ~ ( r2_hidden @ X56 @ ( k6_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X5 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('28',plain,(
    ! [X58: $i] :
      ( ( k1_ordinal1 @ X58 )
      = ( k2_xboole_0 @ X58 @ ( k1_tarski @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X1 )
      | ( X2
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k1_tarski @ sk_A ) @ X1 ) @ X0 )
      | ( X2
        = ( k2_xboole_0 @ X1 @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k1_tarski @ sk_A ) @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k1_tarski @ sk_A ) @ X1 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['37','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ sk_A ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(eq_fact,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['43'])).

thf('45',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['43'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X58: $i] :
      ( ( k1_ordinal1 @ X58 )
      = ( k2_xboole_0 @ X58 @ ( k1_tarski @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('51',plain,
    ( ( k1_ordinal1 @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['0','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('55',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('56',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('58',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('59',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('60',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( zip_tseitin_0 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 )
      | ( r2_hidden @ X46 @ X55 )
      | ( X55
       != ( k6_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( r2_hidden @ X46 @ ( k6_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 ) )
      | ( zip_tseitin_0 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X37 != X36 )
      | ~ ( zip_tseitin_0 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,(
    ! [X36: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ~ ( zip_tseitin_0 @ X36 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X36 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference('sup+',[status(thm)],['53','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['52','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qPJlCTpXdx
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:35:39 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 1.22/1.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.22/1.46  % Solved by: fo/fo7.sh
% 1.22/1.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.22/1.46  % done 768 iterations in 1.002s
% 1.22/1.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.22/1.46  % SZS output start Refutation
% 1.22/1.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.22/1.46  thf(sk_A_type, type, sk_A: $i).
% 1.22/1.46  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.22/1.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 1.22/1.46                                               $i > $i > $i > $o).
% 1.22/1.46  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.22/1.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.22/1.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.22/1.46  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.22/1.46                                           $i > $i).
% 1.22/1.46  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.22/1.46  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.22/1.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.22/1.46  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.22/1.46  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.22/1.46  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.22/1.46  thf(t10_ordinal1, conjecture,
% 1.22/1.46    (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 1.22/1.46  thf(zf_stmt_0, negated_conjecture,
% 1.22/1.46    (~( ![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )),
% 1.22/1.46    inference('cnf.neg', [status(esa)], [t10_ordinal1])).
% 1.22/1.46  thf('0', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 1.22/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.46  thf(d6_enumset1, axiom,
% 1.22/1.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.22/1.46     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 1.22/1.46       ( ![J:$i]:
% 1.22/1.46         ( ( r2_hidden @ J @ I ) <=>
% 1.22/1.46           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 1.22/1.46                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 1.22/1.46                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 1.22/1.46  thf(zf_stmt_1, axiom,
% 1.22/1.46    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 1.22/1.46     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 1.22/1.46       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 1.22/1.46         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 1.22/1.46         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 1.22/1.46  thf('1', plain,
% 1.22/1.46      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, 
% 1.22/1.46         X44 : $i, X45 : $i]:
% 1.22/1.46         ((zip_tseitin_0 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45)
% 1.22/1.46          | ((X37) = (X38))
% 1.22/1.46          | ((X37) = (X39))
% 1.22/1.46          | ((X37) = (X40))
% 1.22/1.46          | ((X37) = (X41))
% 1.22/1.46          | ((X37) = (X42))
% 1.22/1.46          | ((X37) = (X43))
% 1.22/1.46          | ((X37) = (X44))
% 1.22/1.46          | ((X37) = (X45)))),
% 1.22/1.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.22/1.46  thf(d3_xboole_0, axiom,
% 1.22/1.46    (![A:$i,B:$i,C:$i]:
% 1.22/1.46     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.22/1.46       ( ![D:$i]:
% 1.22/1.46         ( ( r2_hidden @ D @ C ) <=>
% 1.22/1.46           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.22/1.46  thf('2', plain,
% 1.22/1.46      (![X1 : $i, X3 : $i, X5 : $i]:
% 1.22/1.46         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 1.22/1.46          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 1.22/1.46          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 1.22/1.46          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 1.22/1.46      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.22/1.46  thf('3', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.22/1.46          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.22/1.46          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 1.22/1.46      inference('eq_fact', [status(thm)], ['2'])).
% 1.22/1.46  thf('4', plain,
% 1.22/1.46      (![X1 : $i, X3 : $i, X5 : $i]:
% 1.22/1.46         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 1.22/1.46          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 1.22/1.46          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 1.22/1.46      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.22/1.46  thf('5', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 1.22/1.46          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.22/1.46          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.22/1.46          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 1.22/1.46      inference('sup-', [status(thm)], ['3', '4'])).
% 1.22/1.46  thf('6', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.22/1.46          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.22/1.46          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 1.22/1.46      inference('simplify', [status(thm)], ['5'])).
% 1.22/1.46  thf('7', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.22/1.46          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.22/1.46          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 1.22/1.46      inference('eq_fact', [status(thm)], ['2'])).
% 1.22/1.46  thf('8', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 1.22/1.46          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.22/1.46      inference('clc', [status(thm)], ['6', '7'])).
% 1.22/1.46  thf(t70_enumset1, axiom,
% 1.22/1.46    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.22/1.46  thf('9', plain,
% 1.22/1.46      (![X7 : $i, X8 : $i]:
% 1.22/1.46         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 1.22/1.46      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.22/1.46  thf(t69_enumset1, axiom,
% 1.22/1.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.22/1.46  thf('10', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.22/1.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.22/1.46  thf('11', plain,
% 1.22/1.46      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.22/1.46      inference('sup+', [status(thm)], ['9', '10'])).
% 1.22/1.46  thf(t71_enumset1, axiom,
% 1.22/1.46    (![A:$i,B:$i,C:$i]:
% 1.22/1.46     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.22/1.46  thf('12', plain,
% 1.22/1.46      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.22/1.46         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 1.22/1.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.22/1.46  thf(t72_enumset1, axiom,
% 1.22/1.46    (![A:$i,B:$i,C:$i,D:$i]:
% 1.22/1.46     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.22/1.46  thf('13', plain,
% 1.22/1.46      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.22/1.46         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 1.22/1.46           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 1.22/1.46      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.22/1.46  thf(t73_enumset1, axiom,
% 1.22/1.46    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.22/1.46     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.22/1.46       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.22/1.46  thf('14', plain,
% 1.22/1.46      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.22/1.46         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 1.22/1.46           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 1.22/1.46      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.22/1.46  thf(t74_enumset1, axiom,
% 1.22/1.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.22/1.46     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.22/1.46       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.22/1.46  thf('15', plain,
% 1.22/1.46      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.22/1.46         ((k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 1.22/1.46           = (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 1.22/1.46      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.22/1.46  thf(t75_enumset1, axiom,
% 1.22/1.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.22/1.46     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.22/1.46       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 1.22/1.46  thf('16', plain,
% 1.22/1.46      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.22/1.46         ((k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 1.22/1.46           = (k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 1.22/1.46      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.22/1.46  thf(zf_stmt_2, type, zip_tseitin_0 :
% 1.22/1.46      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 1.22/1.46  thf(zf_stmt_3, axiom,
% 1.22/1.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.22/1.46     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 1.22/1.46       ( ![J:$i]:
% 1.22/1.46         ( ( r2_hidden @ J @ I ) <=>
% 1.22/1.46           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 1.22/1.46  thf('17', plain,
% 1.22/1.46      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, 
% 1.22/1.46         X54 : $i, X55 : $i, X56 : $i]:
% 1.22/1.46         (~ (r2_hidden @ X56 @ X55)
% 1.22/1.46          | ~ (zip_tseitin_0 @ X56 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ 
% 1.22/1.46               X54)
% 1.22/1.46          | ((X55)
% 1.22/1.46              != (k6_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47)))),
% 1.22/1.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.22/1.46  thf('18', plain,
% 1.22/1.46      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, 
% 1.22/1.46         X54 : $i, X56 : $i]:
% 1.22/1.46         (~ (zip_tseitin_0 @ X56 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ 
% 1.22/1.46             X54)
% 1.22/1.46          | ~ (r2_hidden @ X56 @ 
% 1.22/1.46               (k6_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47)))),
% 1.22/1.46      inference('simplify', [status(thm)], ['17'])).
% 1.22/1.46  thf('19', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.22/1.46         (~ (r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.22/1.46          | ~ (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 1.22/1.46      inference('sup-', [status(thm)], ['16', '18'])).
% 1.22/1.46  thf('20', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.22/1.46         (~ (r2_hidden @ X6 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.22/1.46          | ~ (zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X5))),
% 1.22/1.46      inference('sup-', [status(thm)], ['15', '19'])).
% 1.22/1.46  thf('21', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.22/1.46         (~ (r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.22/1.46          | ~ (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4))),
% 1.22/1.46      inference('sup-', [status(thm)], ['14', '20'])).
% 1.22/1.46  thf('22', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.22/1.46         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 1.22/1.46          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3))),
% 1.22/1.46      inference('sup-', [status(thm)], ['13', '21'])).
% 1.22/1.46  thf('23', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.22/1.46         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 1.22/1.46          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2))),
% 1.22/1.46      inference('sup-', [status(thm)], ['12', '22'])).
% 1.22/1.46  thf('24', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.22/1.46          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 1.22/1.46      inference('sup-', [status(thm)], ['11', '23'])).
% 1.22/1.46  thf('25', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.22/1.46          | ~ (zip_tseitin_0 @ (sk_D @ X1 @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ 
% 1.22/1.46               X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 1.22/1.46      inference('sup-', [status(thm)], ['8', '24'])).
% 1.22/1.46  thf('26', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         (((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.22/1.46          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.22/1.46          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.22/1.46          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.22/1.46          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.22/1.46          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.22/1.46          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.22/1.46          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.22/1.46          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.22/1.46      inference('sup-', [status(thm)], ['1', '25'])).
% 1.22/1.46  thf('27', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.22/1.46          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.22/1.46      inference('simplify', [status(thm)], ['26'])).
% 1.22/1.46  thf(d1_ordinal1, axiom,
% 1.22/1.46    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 1.22/1.46  thf('28', plain,
% 1.22/1.46      (![X58 : $i]:
% 1.22/1.46         ((k1_ordinal1 @ X58) = (k2_xboole_0 @ X58 @ (k1_tarski @ X58)))),
% 1.22/1.46      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.22/1.46  thf('29', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 1.22/1.46          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.22/1.46      inference('clc', [status(thm)], ['6', '7'])).
% 1.22/1.46  thf('30', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.22/1.46         (~ (r2_hidden @ X0 @ X1)
% 1.22/1.46          | (r2_hidden @ X0 @ X2)
% 1.22/1.46          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.22/1.46      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.22/1.46  thf('31', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.22/1.46         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 1.22/1.46      inference('simplify', [status(thm)], ['30'])).
% 1.22/1.46  thf('32', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.22/1.46         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 1.22/1.46          | (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 1.22/1.46      inference('sup-', [status(thm)], ['29', '31'])).
% 1.22/1.46  thf('33', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         ((r2_hidden @ (sk_D @ X1 @ X1 @ (k1_tarski @ X0)) @ (k1_ordinal1 @ X0))
% 1.22/1.46          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.22/1.46      inference('sup+', [status(thm)], ['28', '32'])).
% 1.22/1.46  thf('34', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         ((r2_hidden @ X0 @ (k1_ordinal1 @ X0))
% 1.22/1.46          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.22/1.46          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.22/1.46      inference('sup+', [status(thm)], ['27', '33'])).
% 1.22/1.46  thf('35', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.22/1.46          | (r2_hidden @ X0 @ (k1_ordinal1 @ X0)))),
% 1.22/1.46      inference('simplify', [status(thm)], ['34'])).
% 1.22/1.46  thf('36', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 1.22/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.46  thf('37', plain,
% 1.22/1.46      (![X0 : $i]: ((X0) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 1.22/1.46      inference('sup-', [status(thm)], ['35', '36'])).
% 1.22/1.46  thf('38', plain,
% 1.22/1.46      (![X1 : $i, X3 : $i, X5 : $i]:
% 1.22/1.46         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 1.22/1.46          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 1.22/1.46          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 1.22/1.46          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 1.22/1.46      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.22/1.46  thf('39', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.22/1.46         (~ (r2_hidden @ X0 @ X3)
% 1.22/1.46          | (r2_hidden @ X0 @ X2)
% 1.22/1.46          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.22/1.46      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.22/1.46  thf('40', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.22/1.46         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 1.22/1.46      inference('simplify', [status(thm)], ['39'])).
% 1.22/1.46  thf('41', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.22/1.46         ((r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X2)
% 1.22/1.46          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X1)
% 1.22/1.46          | ((X2) = (k2_xboole_0 @ X1 @ X0))
% 1.22/1.46          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 1.22/1.46      inference('sup-', [status(thm)], ['38', '40'])).
% 1.22/1.46  thf('42', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.22/1.46         ((r2_hidden @ (sk_D @ X2 @ (k1_tarski @ sk_A) @ X1) @ X0)
% 1.22/1.46          | ((X2) = (k2_xboole_0 @ X1 @ (k1_tarski @ sk_A)))
% 1.22/1.46          | (r2_hidden @ (sk_D @ X2 @ (k1_tarski @ sk_A) @ X1) @ X1)
% 1.22/1.46          | (r2_hidden @ (sk_D @ X2 @ (k1_tarski @ sk_A) @ X1) @ X2))),
% 1.22/1.46      inference('sup+', [status(thm)], ['37', '41'])).
% 1.22/1.46  thf('43', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         ((r2_hidden @ (sk_D @ X1 @ (k1_tarski @ sk_A) @ X0) @ X1)
% 1.22/1.46          | (r2_hidden @ (sk_D @ X1 @ (k1_tarski @ sk_A) @ X0) @ X0)
% 1.22/1.46          | ((X1) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 1.22/1.46      inference('eq_fact', [status(thm)], ['42'])).
% 1.22/1.46  thf('44', plain,
% 1.22/1.46      (![X0 : $i]:
% 1.22/1.46         (((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 1.22/1.46          | (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ sk_A) @ X0) @ X0))),
% 1.22/1.46      inference('eq_fact', [status(thm)], ['43'])).
% 1.22/1.46  thf('45', plain,
% 1.22/1.46      (![X1 : $i, X3 : $i, X5 : $i]:
% 1.22/1.46         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 1.22/1.46          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 1.22/1.46          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 1.22/1.46      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.22/1.46  thf('46', plain,
% 1.22/1.46      (![X0 : $i]:
% 1.22/1.46         (((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 1.22/1.46          | ~ (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ sk_A) @ X0) @ X0)
% 1.22/1.46          | ((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 1.22/1.46      inference('sup-', [status(thm)], ['44', '45'])).
% 1.22/1.46  thf('47', plain,
% 1.22/1.46      (![X0 : $i]:
% 1.22/1.46         (~ (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ sk_A) @ X0) @ X0)
% 1.22/1.46          | ((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 1.22/1.46      inference('simplify', [status(thm)], ['46'])).
% 1.22/1.46  thf('48', plain,
% 1.22/1.46      (![X0 : $i]:
% 1.22/1.46         (((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 1.22/1.46          | (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ sk_A) @ X0) @ X0))),
% 1.22/1.46      inference('eq_fact', [status(thm)], ['43'])).
% 1.22/1.46  thf('49', plain,
% 1.22/1.46      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 1.22/1.46      inference('clc', [status(thm)], ['47', '48'])).
% 1.22/1.46  thf('50', plain,
% 1.22/1.46      (![X58 : $i]:
% 1.22/1.46         ((k1_ordinal1 @ X58) = (k2_xboole_0 @ X58 @ (k1_tarski @ X58)))),
% 1.22/1.46      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.22/1.46  thf('51', plain, (((k1_ordinal1 @ sk_A) = (sk_A))),
% 1.22/1.46      inference('sup+', [status(thm)], ['49', '50'])).
% 1.22/1.46  thf('52', plain, (~ (r2_hidden @ sk_A @ sk_A)),
% 1.22/1.46      inference('demod', [status(thm)], ['0', '51'])).
% 1.22/1.46  thf('53', plain,
% 1.22/1.46      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 1.22/1.46      inference('clc', [status(thm)], ['47', '48'])).
% 1.22/1.46  thf('54', plain,
% 1.22/1.46      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.22/1.46      inference('sup+', [status(thm)], ['9', '10'])).
% 1.22/1.46  thf('55', plain,
% 1.22/1.46      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.22/1.46         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 1.22/1.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.22/1.46  thf('56', plain,
% 1.22/1.46      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.22/1.46         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 1.22/1.46           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 1.22/1.46      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.22/1.46  thf('57', plain,
% 1.22/1.46      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.22/1.46         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 1.22/1.46           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 1.22/1.46      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.22/1.46  thf('58', plain,
% 1.22/1.46      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.22/1.46         ((k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 1.22/1.46           = (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 1.22/1.46      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.22/1.46  thf('59', plain,
% 1.22/1.46      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.22/1.46         ((k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 1.22/1.46           = (k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 1.22/1.46      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.22/1.46  thf('60', plain,
% 1.22/1.46      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, 
% 1.22/1.46         X53 : $i, X54 : $i, X55 : $i]:
% 1.22/1.46         ((zip_tseitin_0 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54)
% 1.22/1.46          | (r2_hidden @ X46 @ X55)
% 1.22/1.46          | ((X55)
% 1.22/1.46              != (k6_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47)))),
% 1.22/1.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.22/1.46  thf('61', plain,
% 1.22/1.46      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, 
% 1.22/1.46         X53 : $i, X54 : $i]:
% 1.22/1.46         ((r2_hidden @ X46 @ 
% 1.22/1.46           (k6_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47))
% 1.22/1.46          | (zip_tseitin_0 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ 
% 1.22/1.46             X54))),
% 1.22/1.46      inference('simplify', [status(thm)], ['60'])).
% 1.22/1.46  thf('62', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.22/1.46         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.22/1.46          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 1.22/1.46      inference('sup+', [status(thm)], ['59', '61'])).
% 1.22/1.46  thf('63', plain,
% 1.22/1.46      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, 
% 1.22/1.46         X43 : $i, X44 : $i]:
% 1.22/1.46         (((X37) != (X36))
% 1.22/1.46          | ~ (zip_tseitin_0 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ 
% 1.22/1.46               X36))),
% 1.22/1.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.22/1.46  thf('64', plain,
% 1.22/1.46      (![X36 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, 
% 1.22/1.46         X44 : $i]:
% 1.22/1.46         ~ (zip_tseitin_0 @ X36 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X36)),
% 1.22/1.46      inference('simplify', [status(thm)], ['63'])).
% 1.22/1.46  thf('65', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.22/1.46         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 1.22/1.46      inference('sup-', [status(thm)], ['62', '64'])).
% 1.22/1.46  thf('66', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.22/1.46         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.22/1.46      inference('sup+', [status(thm)], ['58', '65'])).
% 1.22/1.46  thf('67', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.22/1.46         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.22/1.46      inference('sup+', [status(thm)], ['57', '66'])).
% 1.22/1.46  thf('68', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.22/1.46         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.22/1.46      inference('sup+', [status(thm)], ['56', '67'])).
% 1.22/1.46  thf('69', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.22/1.46         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.22/1.46      inference('sup+', [status(thm)], ['55', '68'])).
% 1.22/1.46  thf('70', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.22/1.46      inference('sup+', [status(thm)], ['54', '69'])).
% 1.22/1.46  thf('71', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.22/1.46         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 1.22/1.46      inference('simplify', [status(thm)], ['30'])).
% 1.22/1.46  thf('72', plain,
% 1.22/1.46      (![X0 : $i, X1 : $i]:
% 1.22/1.46         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 1.22/1.46      inference('sup-', [status(thm)], ['70', '71'])).
% 1.22/1.46  thf('73', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 1.22/1.46      inference('sup+', [status(thm)], ['53', '72'])).
% 1.22/1.46  thf('74', plain, ($false), inference('demod', [status(thm)], ['52', '73'])).
% 1.22/1.46  
% 1.22/1.46  % SZS output end Refutation
% 1.22/1.46  
% 1.30/1.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
