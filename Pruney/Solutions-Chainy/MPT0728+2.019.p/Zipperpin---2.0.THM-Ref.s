%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N2ERJa6JJZ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:40 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 327 expanded)
%              Number of leaves         :   24 (  98 expanded)
%              Depth                    :   21
%              Number of atoms          : 1092 (4768 expanded)
%              Number of equality atoms :   90 ( 380 expanded)
%              Maximal formula depth    :   23 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      | ( X24 = X25 )
      | ( X24 = X26 )
      | ( X24 = X27 )
      | ( X24 = X28 )
      | ( X24 = X29 )
      | ( X24 = X30 )
      | ( X24 = X31 )
      | ( X24 = X32 ) ) ),
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

thf(t86_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k6_enumset1 @ X16 @ X16 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t86_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X43 @ X42 )
      | ~ ( zip_tseitin_0 @ X43 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 )
      | ( X42
       != ( k6_enumset1 @ X41 @ X40 @ X39 @ X38 @ X37 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 )
      | ~ ( r2_hidden @ X43 @ ( k6_enumset1 @ X41 @ X40 @ X39 @ X38 @ X37 @ X36 @ X35 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','20'])).

thf('22',plain,(
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
    inference('sup-',[status(thm)],['1','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('24',plain,(
    ! [X45: $i] :
      ( ( k1_ordinal1 @ X45 )
      = ( k2_xboole_0 @ X45 @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X1 )
      | ( X2
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k1_tarski @ sk_A ) @ X1 ) @ X0 )
      | ( X2
        = ( k2_xboole_0 @ X1 @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k1_tarski @ sk_A ) @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k1_tarski @ sk_A ) @ X1 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ sk_A ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(eq_fact,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['39'])).

thf('41',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['39'])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X45: $i] :
      ( ( k1_ordinal1 @ X45 )
      = ( k2_xboole_0 @ X45 @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('47',plain,
    ( ( k1_ordinal1 @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['0','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('51',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('52',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('53',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k6_enumset1 @ X16 @ X16 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t86_enumset1])).

thf('54',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 )
      | ( r2_hidden @ X33 @ X42 )
      | ( X42
       != ( k6_enumset1 @ X41 @ X40 @ X39 @ X38 @ X37 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( r2_hidden @ X33 @ ( k6_enumset1 @ X41 @ X40 @ X39 @ X38 @ X37 @ X36 @ X35 @ X34 ) )
      | ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X24 != X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,(
    ! [X23: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X23 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference('sup+',[status(thm)],['49','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['48','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N2ERJa6JJZ
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.13  % Solved by: fo/fo7.sh
% 0.90/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.13  % done 807 iterations in 0.680s
% 0.90/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.13  % SZS output start Refutation
% 0.90/1.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.13  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.90/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.13  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.13  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.13  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.90/1.13                                           $i > $i).
% 0.90/1.13  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.90/1.13  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.90/1.13  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.13  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.90/1.13  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.90/1.13                                               $i > $i > $i > $o).
% 0.90/1.13  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.90/1.13  thf(t10_ordinal1, conjecture,
% 0.90/1.13    (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.90/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.13    (~( ![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )),
% 0.90/1.13    inference('cnf.neg', [status(esa)], [t10_ordinal1])).
% 0.90/1.13  thf('0', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(d6_enumset1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.90/1.13     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.90/1.13       ( ![J:$i]:
% 0.90/1.13         ( ( r2_hidden @ J @ I ) <=>
% 0.90/1.13           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.90/1.13                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.90/1.13                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.90/1.13  thf(zf_stmt_1, axiom,
% 0.90/1.13    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.90/1.13     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.90/1.13       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.90/1.13         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.90/1.13         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.90/1.13  thf('1', plain,
% 0.90/1.13      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, 
% 0.90/1.13         X31 : $i, X32 : $i]:
% 0.90/1.13         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 0.90/1.13          | ((X24) = (X25))
% 0.90/1.13          | ((X24) = (X26))
% 0.90/1.13          | ((X24) = (X27))
% 0.90/1.13          | ((X24) = (X28))
% 0.90/1.13          | ((X24) = (X29))
% 0.90/1.13          | ((X24) = (X30))
% 0.90/1.13          | ((X24) = (X31))
% 0.90/1.13          | ((X24) = (X32)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.13  thf(d3_xboole_0, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.90/1.13       ( ![D:$i]:
% 0.90/1.13         ( ( r2_hidden @ D @ C ) <=>
% 0.90/1.13           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.90/1.13  thf('2', plain,
% 0.90/1.13      (![X1 : $i, X3 : $i, X5 : $i]:
% 0.90/1.13         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 0.90/1.13          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 0.90/1.13          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 0.90/1.13          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.90/1.13  thf('3', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.90/1.13          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.90/1.13          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.90/1.13      inference('eq_fact', [status(thm)], ['2'])).
% 0.90/1.13  thf('4', plain,
% 0.90/1.13      (![X1 : $i, X3 : $i, X5 : $i]:
% 0.90/1.13         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 0.90/1.13          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 0.90/1.13          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.90/1.13  thf('5', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.90/1.13          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.90/1.13          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.90/1.13          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['3', '4'])).
% 0.90/1.13  thf('6', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.90/1.13          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.90/1.13          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.90/1.13      inference('simplify', [status(thm)], ['5'])).
% 0.90/1.13  thf('7', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.90/1.13          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.90/1.13          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.90/1.13      inference('eq_fact', [status(thm)], ['2'])).
% 0.90/1.13  thf('8', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.90/1.13          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.90/1.13      inference('clc', [status(thm)], ['6', '7'])).
% 0.90/1.13  thf(t70_enumset1, axiom,
% 0.90/1.13    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.90/1.13  thf('9', plain,
% 0.90/1.13      (![X7 : $i, X8 : $i]:
% 0.90/1.13         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.90/1.13      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.90/1.13  thf(t69_enumset1, axiom,
% 0.90/1.13    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.90/1.13  thf('10', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.90/1.13      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.13  thf('11', plain,
% 0.90/1.13      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.90/1.13      inference('sup+', [status(thm)], ['9', '10'])).
% 0.90/1.13  thf(t71_enumset1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.90/1.13  thf('12', plain,
% 0.90/1.13      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.13         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.90/1.13      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.90/1.13  thf(t72_enumset1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.13     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.90/1.13  thf('13', plain,
% 0.90/1.13      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.90/1.13         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 0.90/1.13           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 0.90/1.13      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.90/1.13  thf(t86_enumset1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.90/1.13     ( ( k6_enumset1 @ A @ A @ A @ A @ B @ C @ D @ E ) =
% 0.90/1.13       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.90/1.13  thf('14', plain,
% 0.90/1.13      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.90/1.13         ((k6_enumset1 @ X16 @ X16 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.90/1.13           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.90/1.13      inference('cnf', [status(esa)], [t86_enumset1])).
% 0.90/1.13  thf(zf_stmt_2, type, zip_tseitin_0 :
% 0.90/1.13      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.90/1.13  thf(zf_stmt_3, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.90/1.13     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.90/1.13       ( ![J:$i]:
% 0.90/1.13         ( ( r2_hidden @ J @ I ) <=>
% 0.90/1.13           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.90/1.13  thf('15', plain,
% 0.90/1.13      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, 
% 0.90/1.13         X41 : $i, X42 : $i, X43 : $i]:
% 0.90/1.13         (~ (r2_hidden @ X43 @ X42)
% 0.90/1.13          | ~ (zip_tseitin_0 @ X43 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ 
% 0.90/1.13               X41)
% 0.90/1.13          | ((X42)
% 0.90/1.13              != (k6_enumset1 @ X41 @ X40 @ X39 @ X38 @ X37 @ X36 @ X35 @ X34)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.13  thf('16', plain,
% 0.90/1.13      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, 
% 0.90/1.13         X41 : $i, X43 : $i]:
% 0.90/1.13         (~ (zip_tseitin_0 @ X43 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ 
% 0.90/1.13             X41)
% 0.90/1.13          | ~ (r2_hidden @ X43 @ 
% 0.90/1.13               (k6_enumset1 @ X41 @ X40 @ X39 @ X38 @ X37 @ X36 @ X35 @ X34)))),
% 0.90/1.13      inference('simplify', [status(thm)], ['15'])).
% 0.90/1.13  thf('17', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.90/1.13         (~ (r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.90/1.13          | ~ (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4))),
% 0.90/1.13      inference('sup-', [status(thm)], ['14', '16'])).
% 0.90/1.13  thf('18', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.13         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.90/1.13          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3))),
% 0.90/1.13      inference('sup-', [status(thm)], ['13', '17'])).
% 0.90/1.13  thf('19', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.13         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.90/1.13          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2))),
% 0.90/1.13      inference('sup-', [status(thm)], ['12', '18'])).
% 0.90/1.13  thf('20', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.90/1.13          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['11', '19'])).
% 0.90/1.13  thf('21', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.90/1.13          | ~ (zip_tseitin_0 @ (sk_D @ X1 @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ 
% 0.90/1.13               X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['8', '20'])).
% 0.90/1.13  thf('22', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.90/1.13          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.90/1.13          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.90/1.13          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.90/1.13          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.90/1.13          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.90/1.13          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.90/1.13          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.90/1.13          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['1', '21'])).
% 0.90/1.13  thf('23', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.90/1.13          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.90/1.13      inference('simplify', [status(thm)], ['22'])).
% 0.90/1.13  thf(d1_ordinal1, axiom,
% 0.90/1.13    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.90/1.13  thf('24', plain,
% 0.90/1.13      (![X45 : $i]:
% 0.90/1.13         ((k1_ordinal1 @ X45) = (k2_xboole_0 @ X45 @ (k1_tarski @ X45)))),
% 0.90/1.13      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.90/1.13  thf('25', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.90/1.13          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.90/1.13      inference('clc', [status(thm)], ['6', '7'])).
% 0.90/1.13  thf('26', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.13         (~ (r2_hidden @ X0 @ X1)
% 0.90/1.13          | (r2_hidden @ X0 @ X2)
% 0.90/1.13          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.90/1.13  thf('27', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.90/1.13         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.90/1.13      inference('simplify', [status(thm)], ['26'])).
% 0.90/1.13  thf('28', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 0.90/1.13          | (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['25', '27'])).
% 0.90/1.13  thf('29', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         ((r2_hidden @ (sk_D @ X1 @ X1 @ (k1_tarski @ X0)) @ (k1_ordinal1 @ X0))
% 0.90/1.13          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.90/1.13      inference('sup+', [status(thm)], ['24', '28'])).
% 0.90/1.13  thf('30', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         ((r2_hidden @ X0 @ (k1_ordinal1 @ X0))
% 0.90/1.13          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.90/1.13          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.90/1.13      inference('sup+', [status(thm)], ['23', '29'])).
% 0.90/1.13  thf('31', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.90/1.13          | (r2_hidden @ X0 @ (k1_ordinal1 @ X0)))),
% 0.90/1.13      inference('simplify', [status(thm)], ['30'])).
% 0.90/1.13  thf('32', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('33', plain,
% 0.90/1.13      (![X0 : $i]: ((X0) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['31', '32'])).
% 0.90/1.13  thf('34', plain,
% 0.90/1.13      (![X1 : $i, X3 : $i, X5 : $i]:
% 0.90/1.13         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 0.90/1.13          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 0.90/1.13          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 0.90/1.13          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.90/1.13  thf('35', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.13         (~ (r2_hidden @ X0 @ X3)
% 0.90/1.13          | (r2_hidden @ X0 @ X2)
% 0.90/1.13          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.90/1.13  thf('36', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.90/1.13         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.90/1.13      inference('simplify', [status(thm)], ['35'])).
% 0.90/1.13  thf('37', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.13         ((r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X2)
% 0.90/1.13          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X1)
% 0.90/1.13          | ((X2) = (k2_xboole_0 @ X1 @ X0))
% 0.90/1.13          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['34', '36'])).
% 0.90/1.13  thf('38', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         ((r2_hidden @ (sk_D @ X2 @ (k1_tarski @ sk_A) @ X1) @ X0)
% 0.90/1.13          | ((X2) = (k2_xboole_0 @ X1 @ (k1_tarski @ sk_A)))
% 0.90/1.13          | (r2_hidden @ (sk_D @ X2 @ (k1_tarski @ sk_A) @ X1) @ X1)
% 0.90/1.13          | (r2_hidden @ (sk_D @ X2 @ (k1_tarski @ sk_A) @ X1) @ X2))),
% 0.90/1.13      inference('sup+', [status(thm)], ['33', '37'])).
% 0.90/1.13  thf('39', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         ((r2_hidden @ (sk_D @ X1 @ (k1_tarski @ sk_A) @ X0) @ X1)
% 0.90/1.13          | (r2_hidden @ (sk_D @ X1 @ (k1_tarski @ sk_A) @ X0) @ X0)
% 0.90/1.13          | ((X1) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 0.90/1.13      inference('eq_fact', [status(thm)], ['38'])).
% 0.90/1.13  thf('40', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.90/1.13          | (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ sk_A) @ X0) @ X0))),
% 0.90/1.13      inference('eq_fact', [status(thm)], ['39'])).
% 0.90/1.13  thf('41', plain,
% 0.90/1.13      (![X1 : $i, X3 : $i, X5 : $i]:
% 0.90/1.13         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 0.90/1.13          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 0.90/1.13          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.90/1.13  thf('42', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.90/1.13          | ~ (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ sk_A) @ X0) @ X0)
% 0.90/1.13          | ((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['40', '41'])).
% 0.90/1.13  thf('43', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ sk_A) @ X0) @ X0)
% 0.90/1.13          | ((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 0.90/1.13      inference('simplify', [status(thm)], ['42'])).
% 0.90/1.13  thf('44', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.90/1.13          | (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ sk_A) @ X0) @ X0))),
% 0.90/1.13      inference('eq_fact', [status(thm)], ['39'])).
% 0.90/1.13  thf('45', plain,
% 0.90/1.13      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 0.90/1.13      inference('clc', [status(thm)], ['43', '44'])).
% 0.90/1.13  thf('46', plain,
% 0.90/1.13      (![X45 : $i]:
% 0.90/1.13         ((k1_ordinal1 @ X45) = (k2_xboole_0 @ X45 @ (k1_tarski @ X45)))),
% 0.90/1.13      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.90/1.13  thf('47', plain, (((k1_ordinal1 @ sk_A) = (sk_A))),
% 0.90/1.13      inference('sup+', [status(thm)], ['45', '46'])).
% 0.90/1.13  thf('48', plain, (~ (r2_hidden @ sk_A @ sk_A)),
% 0.90/1.13      inference('demod', [status(thm)], ['0', '47'])).
% 0.90/1.13  thf('49', plain,
% 0.90/1.13      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 0.90/1.13      inference('clc', [status(thm)], ['43', '44'])).
% 0.90/1.13  thf('50', plain,
% 0.90/1.13      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.90/1.13      inference('sup+', [status(thm)], ['9', '10'])).
% 0.90/1.13  thf('51', plain,
% 0.90/1.13      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.13         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.90/1.13      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.90/1.13  thf('52', plain,
% 0.90/1.13      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.90/1.13         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 0.90/1.13           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 0.90/1.13      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.90/1.13  thf('53', plain,
% 0.90/1.13      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.90/1.13         ((k6_enumset1 @ X16 @ X16 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.90/1.13           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.90/1.13      inference('cnf', [status(esa)], [t86_enumset1])).
% 0.90/1.13  thf('54', plain,
% 0.90/1.13      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 0.90/1.13         X40 : $i, X41 : $i, X42 : $i]:
% 0.90/1.13         ((zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41)
% 0.90/1.13          | (r2_hidden @ X33 @ X42)
% 0.90/1.13          | ((X42)
% 0.90/1.13              != (k6_enumset1 @ X41 @ X40 @ X39 @ X38 @ X37 @ X36 @ X35 @ X34)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.13  thf('55', plain,
% 0.90/1.13      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 0.90/1.13         X40 : $i, X41 : $i]:
% 0.90/1.13         ((r2_hidden @ X33 @ 
% 0.90/1.13           (k6_enumset1 @ X41 @ X40 @ X39 @ X38 @ X37 @ X36 @ X35 @ X34))
% 0.90/1.13          | (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ 
% 0.90/1.13             X41))),
% 0.90/1.13      inference('simplify', [status(thm)], ['54'])).
% 0.90/1.13  thf('56', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.90/1.13         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.90/1.13          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4))),
% 0.90/1.13      inference('sup+', [status(thm)], ['53', '55'])).
% 0.90/1.13  thf('57', plain,
% 0.90/1.13      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, 
% 0.90/1.13         X30 : $i, X31 : $i]:
% 0.90/1.13         (((X24) != (X23))
% 0.90/1.13          | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ 
% 0.90/1.13               X23))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.13  thf('58', plain,
% 0.90/1.13      (![X23 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, 
% 0.90/1.13         X31 : $i]:
% 0.90/1.13         ~ (zip_tseitin_0 @ X23 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X23)),
% 0.90/1.13      inference('simplify', [status(thm)], ['57'])).
% 0.90/1.13  thf('59', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.13         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.90/1.13      inference('sup-', [status(thm)], ['56', '58'])).
% 0.90/1.13  thf('60', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.13         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.90/1.13      inference('sup+', [status(thm)], ['52', '59'])).
% 0.90/1.13  thf('61', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.90/1.13      inference('sup+', [status(thm)], ['51', '60'])).
% 0.90/1.13  thf('62', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.90/1.13      inference('sup+', [status(thm)], ['50', '61'])).
% 0.90/1.13  thf('63', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.90/1.13         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.90/1.13      inference('simplify', [status(thm)], ['26'])).
% 0.90/1.13  thf('64', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['62', '63'])).
% 0.90/1.13  thf('65', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.90/1.13      inference('sup+', [status(thm)], ['49', '64'])).
% 0.90/1.13  thf('66', plain, ($false), inference('demod', [status(thm)], ['48', '65'])).
% 0.90/1.13  
% 0.90/1.13  % SZS output end Refutation
% 0.90/1.13  
% 0.90/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
