%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vkuXkSetuY

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:40 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 355 expanded)
%              Number of leaves         :   24 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          : 1085 (4832 expanded)
%              Number of equality atoms :   92 ( 387 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

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

thf(zf_stmt_1,axiom,(
    ! [H: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A )
    <=> ( ( H != A )
        & ( H != B )
        & ( H != C )
        & ( H != D )
        & ( H != E )
        & ( H != F ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      | ( X24 = X25 )
      | ( X24 = X26 )
      | ( X24 = X27 )
      | ( X24 = X28 )
      | ( X24 = X29 )
      | ( X24 = X30 ) ) ),
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

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X39 @ X38 )
      | ~ ( zip_tseitin_0 @ X39 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      | ( X38
       != ( k4_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      | ~ ( r2_hidden @ X39 @ ( k4_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
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
    ! [X41: $i] :
      ( ( k1_ordinal1 @ X41 )
      = ( k2_xboole_0 @ X41 @ ( k1_tarski @ X41 ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['34'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('45',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 @ X1 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X0 @ X1 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['33','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X41: $i] :
      ( ( k1_ordinal1 @ X41 )
      = ( k2_xboole_0 @ X41 @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('54',plain,
    ( ( k1_ordinal1 @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['0','54'])).

thf('56',plain,
    ( ( k1_ordinal1 @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['52','53'])).

thf('57',plain,(
    ! [X41: $i] :
      ( ( k1_ordinal1 @ X41 )
      = ( k2_xboole_0 @ X41 @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('59',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('60',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('61',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('62',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      | ( r2_hidden @ X31 @ X38 )
      | ( X38
       != ( k4_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('63',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X31 @ ( k4_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32 ) )
      | ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['61','63'])).

thf('65',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X24 != X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('66',plain,(
    ! [X23: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X25 @ X26 @ X27 @ X28 @ X29 @ X23 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','72'])).

thf('74',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference('sup+',[status(thm)],['56','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['55','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vkuXkSetuY
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.19/1.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.19/1.39  % Solved by: fo/fo7.sh
% 1.19/1.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.39  % done 798 iterations in 0.933s
% 1.19/1.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.19/1.39  % SZS output start Refutation
% 1.19/1.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.19/1.39  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.19/1.39  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.19/1.39  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.19/1.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.19/1.39  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.19/1.39  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.19/1.39  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.19/1.39  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.39  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 1.19/1.39  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.19/1.39  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.19/1.39  thf(t10_ordinal1, conjecture,
% 1.19/1.39    (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 1.19/1.39  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.39    (~( ![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )),
% 1.19/1.39    inference('cnf.neg', [status(esa)], [t10_ordinal1])).
% 1.19/1.39  thf('0', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(d4_enumset1, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.19/1.39     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 1.19/1.39       ( ![H:$i]:
% 1.19/1.39         ( ( r2_hidden @ H @ G ) <=>
% 1.19/1.39           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 1.19/1.39                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 1.19/1.39  thf(zf_stmt_1, axiom,
% 1.19/1.39    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 1.19/1.39     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 1.19/1.39       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 1.19/1.39         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 1.19/1.39  thf('1', plain,
% 1.19/1.39      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.19/1.39         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 1.19/1.39          | ((X24) = (X25))
% 1.19/1.39          | ((X24) = (X26))
% 1.19/1.39          | ((X24) = (X27))
% 1.19/1.39          | ((X24) = (X28))
% 1.19/1.39          | ((X24) = (X29))
% 1.19/1.39          | ((X24) = (X30)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.19/1.39  thf(d3_xboole_0, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i]:
% 1.19/1.39     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.19/1.39       ( ![D:$i]:
% 1.19/1.39         ( ( r2_hidden @ D @ C ) <=>
% 1.19/1.39           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.19/1.39  thf('2', plain,
% 1.19/1.39      (![X1 : $i, X3 : $i, X5 : $i]:
% 1.19/1.39         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 1.19/1.39          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 1.19/1.39          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 1.19/1.39          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 1.19/1.39      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.19/1.39  thf('3', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.19/1.39          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.19/1.39          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 1.19/1.39      inference('eq_fact', [status(thm)], ['2'])).
% 1.19/1.39  thf('4', plain,
% 1.19/1.39      (![X1 : $i, X3 : $i, X5 : $i]:
% 1.19/1.39         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 1.19/1.39          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 1.19/1.39          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 1.19/1.39      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.19/1.39  thf('5', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 1.19/1.39          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.19/1.39          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.19/1.39          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['3', '4'])).
% 1.19/1.39  thf('6', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.19/1.39          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.19/1.39          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 1.19/1.39      inference('simplify', [status(thm)], ['5'])).
% 1.19/1.39  thf('7', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.19/1.39          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.19/1.39          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 1.19/1.39      inference('eq_fact', [status(thm)], ['2'])).
% 1.19/1.39  thf('8', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 1.19/1.39          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.19/1.39      inference('clc', [status(thm)], ['6', '7'])).
% 1.19/1.39  thf(t70_enumset1, axiom,
% 1.19/1.39    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.19/1.39  thf('9', plain,
% 1.19/1.39      (![X7 : $i, X8 : $i]:
% 1.19/1.39         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 1.19/1.39      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.19/1.39  thf(t69_enumset1, axiom,
% 1.19/1.39    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.19/1.39  thf('10', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.19/1.39      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.19/1.39  thf('11', plain,
% 1.19/1.39      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.19/1.39      inference('sup+', [status(thm)], ['9', '10'])).
% 1.19/1.39  thf(t71_enumset1, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i]:
% 1.19/1.39     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.19/1.39  thf('12', plain,
% 1.19/1.39      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.19/1.39         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 1.19/1.39      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.19/1.39  thf(t72_enumset1, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.39     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.19/1.39  thf('13', plain,
% 1.19/1.39      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.19/1.39         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 1.19/1.39           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 1.19/1.39      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.19/1.39  thf(t73_enumset1, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.19/1.39     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.19/1.39       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.19/1.39  thf('14', plain,
% 1.19/1.39      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.19/1.39         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 1.19/1.39           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 1.19/1.39      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.19/1.39  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 1.19/1.39  thf(zf_stmt_3, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.19/1.39     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 1.19/1.39       ( ![H:$i]:
% 1.19/1.39         ( ( r2_hidden @ H @ G ) <=>
% 1.19/1.39           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 1.19/1.39  thf('15', plain,
% 1.19/1.39      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 1.19/1.39         X39 : $i]:
% 1.19/1.39         (~ (r2_hidden @ X39 @ X38)
% 1.19/1.39          | ~ (zip_tseitin_0 @ X39 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 1.19/1.39          | ((X38) != (k4_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.19/1.39  thf('16', plain,
% 1.19/1.39      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X39 : $i]:
% 1.19/1.39         (~ (zip_tseitin_0 @ X39 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 1.19/1.39          | ~ (r2_hidden @ X39 @ 
% 1.19/1.39               (k4_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32)))),
% 1.19/1.39      inference('simplify', [status(thm)], ['15'])).
% 1.19/1.39  thf('17', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.19/1.39         (~ (r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.19/1.39          | ~ (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 1.19/1.39      inference('sup-', [status(thm)], ['14', '16'])).
% 1.19/1.39  thf('18', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.19/1.39         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 1.19/1.39          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3))),
% 1.19/1.39      inference('sup-', [status(thm)], ['13', '17'])).
% 1.19/1.39  thf('19', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.39         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 1.19/1.39          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2))),
% 1.19/1.39      inference('sup-', [status(thm)], ['12', '18'])).
% 1.19/1.39  thf('20', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.19/1.39          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 1.19/1.39      inference('sup-', [status(thm)], ['11', '19'])).
% 1.19/1.39  thf('21', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.19/1.39          | ~ (zip_tseitin_0 @ (sk_D @ X1 @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ 
% 1.19/1.39               X0 @ X0 @ X0 @ X0))),
% 1.19/1.39      inference('sup-', [status(thm)], ['8', '20'])).
% 1.19/1.39  thf('22', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.19/1.39          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.19/1.39          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.19/1.39          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.19/1.39          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.19/1.39          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.19/1.39          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['1', '21'])).
% 1.19/1.39  thf('23', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.19/1.39          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.19/1.39      inference('simplify', [status(thm)], ['22'])).
% 1.19/1.39  thf(d1_ordinal1, axiom,
% 1.19/1.39    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 1.19/1.39  thf('24', plain,
% 1.19/1.39      (![X41 : $i]:
% 1.19/1.39         ((k1_ordinal1 @ X41) = (k2_xboole_0 @ X41 @ (k1_tarski @ X41)))),
% 1.19/1.39      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.19/1.39  thf('25', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 1.19/1.39          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.19/1.39      inference('clc', [status(thm)], ['6', '7'])).
% 1.19/1.39  thf('26', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.39         (~ (r2_hidden @ X0 @ X1)
% 1.19/1.39          | (r2_hidden @ X0 @ X2)
% 1.19/1.39          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.19/1.39      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.19/1.39  thf('27', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.19/1.39         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 1.19/1.39      inference('simplify', [status(thm)], ['26'])).
% 1.19/1.39  thf('28', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.39         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 1.19/1.39          | (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['25', '27'])).
% 1.19/1.39  thf('29', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((r2_hidden @ (sk_D @ X1 @ X1 @ (k1_tarski @ X0)) @ (k1_ordinal1 @ X0))
% 1.19/1.39          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.19/1.39      inference('sup+', [status(thm)], ['24', '28'])).
% 1.19/1.39  thf('30', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((r2_hidden @ X0 @ (k1_ordinal1 @ X0))
% 1.19/1.39          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.19/1.39          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.19/1.39      inference('sup+', [status(thm)], ['23', '29'])).
% 1.19/1.39  thf('31', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.19/1.39          | (r2_hidden @ X0 @ (k1_ordinal1 @ X0)))),
% 1.19/1.39      inference('simplify', [status(thm)], ['30'])).
% 1.19/1.39  thf('32', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('33', plain,
% 1.19/1.39      (![X0 : $i]: ((X0) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 1.19/1.39      inference('sup-', [status(thm)], ['31', '32'])).
% 1.19/1.39  thf('34', plain,
% 1.19/1.39      (![X1 : $i, X3 : $i, X5 : $i]:
% 1.19/1.39         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 1.19/1.39          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 1.19/1.39          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 1.19/1.39          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 1.19/1.39      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.19/1.39  thf('35', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.19/1.39          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.19/1.39          | ((X0) = (k2_xboole_0 @ X0 @ X1)))),
% 1.19/1.39      inference('eq_fact', [status(thm)], ['34'])).
% 1.19/1.39  thf('36', plain,
% 1.19/1.39      (![X1 : $i, X3 : $i, X5 : $i]:
% 1.19/1.39         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 1.19/1.39          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 1.19/1.39          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 1.19/1.39      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.19/1.39  thf('37', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 1.19/1.39          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.19/1.39          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.19/1.39          | ((X0) = (k2_xboole_0 @ X0 @ X1)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['35', '36'])).
% 1.19/1.39  thf('38', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.19/1.39          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.19/1.39          | ((X0) = (k2_xboole_0 @ X0 @ X1)))),
% 1.19/1.39      inference('simplify', [status(thm)], ['37'])).
% 1.19/1.39  thf('39', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.19/1.39          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.19/1.39          | ((X0) = (k2_xboole_0 @ X0 @ X1)))),
% 1.19/1.39      inference('eq_fact', [status(thm)], ['34'])).
% 1.19/1.39  thf('40', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 1.19/1.39          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.19/1.39      inference('clc', [status(thm)], ['38', '39'])).
% 1.19/1.39  thf('41', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.39         (~ (r2_hidden @ X0 @ X3)
% 1.19/1.39          | (r2_hidden @ X0 @ X2)
% 1.19/1.39          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.19/1.39      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.19/1.39  thf('42', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.19/1.39         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 1.19/1.39      inference('simplify', [status(thm)], ['41'])).
% 1.19/1.39  thf('43', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.39         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 1.19/1.39          | (r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['40', '42'])).
% 1.19/1.39  thf('44', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 1.19/1.39          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.19/1.39      inference('clc', [status(thm)], ['38', '39'])).
% 1.19/1.39  thf('45', plain,
% 1.19/1.39      (![X1 : $i, X3 : $i, X5 : $i]:
% 1.19/1.39         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 1.19/1.39          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 1.19/1.39          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 1.19/1.39      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.19/1.39  thf('46', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 1.19/1.39          | ~ (r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ X1)
% 1.19/1.39          | ((X1) = (k2_xboole_0 @ X1 @ X0)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['44', '45'])).
% 1.19/1.39  thf('47', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (~ (r2_hidden @ (sk_D @ X1 @ X0 @ X1) @ X1)
% 1.19/1.39          | ((X1) = (k2_xboole_0 @ X1 @ X0)))),
% 1.19/1.39      inference('simplify', [status(thm)], ['46'])).
% 1.19/1.39  thf('48', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (((k2_xboole_0 @ X1 @ X0)
% 1.19/1.39            = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 1.19/1.39          | ((k2_xboole_0 @ X1 @ X0)
% 1.19/1.39              = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['43', '47'])).
% 1.19/1.39  thf('49', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((k2_xboole_0 @ X1 @ X0)
% 1.19/1.39           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 1.19/1.39      inference('simplify', [status(thm)], ['48'])).
% 1.19/1.39  thf('50', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         ((k2_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 1.19/1.39           = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 1.19/1.39      inference('sup+', [status(thm)], ['33', '49'])).
% 1.19/1.39  thf('51', plain,
% 1.19/1.39      (![X0 : $i]: ((X0) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 1.19/1.39      inference('sup-', [status(thm)], ['31', '32'])).
% 1.19/1.39  thf('52', plain,
% 1.19/1.39      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 1.19/1.39      inference('demod', [status(thm)], ['50', '51'])).
% 1.19/1.39  thf('53', plain,
% 1.19/1.39      (![X41 : $i]:
% 1.19/1.39         ((k1_ordinal1 @ X41) = (k2_xboole_0 @ X41 @ (k1_tarski @ X41)))),
% 1.19/1.39      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.19/1.39  thf('54', plain, (((k1_ordinal1 @ sk_A) = (sk_A))),
% 1.19/1.39      inference('sup+', [status(thm)], ['52', '53'])).
% 1.19/1.39  thf('55', plain, (~ (r2_hidden @ sk_A @ sk_A)),
% 1.19/1.39      inference('demod', [status(thm)], ['0', '54'])).
% 1.19/1.39  thf('56', plain, (((k1_ordinal1 @ sk_A) = (sk_A))),
% 1.19/1.39      inference('sup+', [status(thm)], ['52', '53'])).
% 1.19/1.39  thf('57', plain,
% 1.19/1.39      (![X41 : $i]:
% 1.19/1.39         ((k1_ordinal1 @ X41) = (k2_xboole_0 @ X41 @ (k1_tarski @ X41)))),
% 1.19/1.39      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.19/1.39  thf('58', plain,
% 1.19/1.39      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.19/1.39      inference('sup+', [status(thm)], ['9', '10'])).
% 1.19/1.39  thf('59', plain,
% 1.19/1.39      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.19/1.39         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 1.19/1.39      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.19/1.39  thf('60', plain,
% 1.19/1.39      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.19/1.39         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 1.19/1.39           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 1.19/1.39      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.19/1.39  thf('61', plain,
% 1.19/1.39      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.19/1.39         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 1.19/1.39           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 1.19/1.39      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.19/1.39  thf('62', plain,
% 1.19/1.39      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, 
% 1.19/1.39         X38 : $i]:
% 1.19/1.39         ((zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 1.19/1.39          | (r2_hidden @ X31 @ X38)
% 1.19/1.39          | ((X38) != (k4_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.19/1.39  thf('63', plain,
% 1.19/1.39      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.19/1.39         ((r2_hidden @ X31 @ (k4_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32))
% 1.19/1.39          | (zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 1.19/1.39      inference('simplify', [status(thm)], ['62'])).
% 1.19/1.39  thf('64', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.19/1.39         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.19/1.39          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 1.19/1.39      inference('sup+', [status(thm)], ['61', '63'])).
% 1.19/1.39  thf('65', plain,
% 1.19/1.39      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.19/1.39         (((X24) != (X23))
% 1.19/1.39          | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X23))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.19/1.39  thf('66', plain,
% 1.19/1.39      (![X23 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.19/1.39         ~ (zip_tseitin_0 @ X23 @ X25 @ X26 @ X27 @ X28 @ X29 @ X23)),
% 1.19/1.39      inference('simplify', [status(thm)], ['65'])).
% 1.19/1.39  thf('67', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.19/1.39         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 1.19/1.39      inference('sup-', [status(thm)], ['64', '66'])).
% 1.19/1.39  thf('68', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.19/1.39         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.19/1.39      inference('sup+', [status(thm)], ['60', '67'])).
% 1.19/1.39  thf('69', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.39         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.19/1.39      inference('sup+', [status(thm)], ['59', '68'])).
% 1.19/1.39  thf('70', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.19/1.39      inference('sup+', [status(thm)], ['58', '69'])).
% 1.19/1.39  thf('71', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.19/1.39         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 1.19/1.39      inference('simplify', [status(thm)], ['26'])).
% 1.19/1.39  thf('72', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['70', '71'])).
% 1.19/1.39  thf('73', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 1.19/1.39      inference('sup+', [status(thm)], ['57', '72'])).
% 1.19/1.39  thf('74', plain, ((r2_hidden @ sk_A @ sk_A)),
% 1.19/1.39      inference('sup+', [status(thm)], ['56', '73'])).
% 1.19/1.39  thf('75', plain, ($false), inference('demod', [status(thm)], ['55', '74'])).
% 1.19/1.39  
% 1.19/1.39  % SZS output end Refutation
% 1.19/1.39  
% 1.19/1.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
