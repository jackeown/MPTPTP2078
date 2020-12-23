%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o7zdtsnCcK

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 435 expanded)
%              Number of leaves         :   22 ( 143 expanded)
%              Depth                    :   15
%              Number of atoms          :  935 (7556 expanded)
%              Number of equality atoms :   96 ( 632 expanded)
%              Maximal formula depth    :   25 (  12 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d7_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i,J: $i] :
      ( ( J
        = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) )
    <=> ! [K: $i] :
          ( ( r2_hidden @ K @ J )
        <=> ~ ( ( K != I )
              & ( K != H )
              & ( K != G )
              & ( K != F )
              & ( K != E )
              & ( K != D )
              & ( K != C )
              & ( K != B )
              & ( K != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [K: $i,I: $i,H: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( K != A )
        & ( K != B )
        & ( K != C )
        & ( K != D )
        & ( K != E )
        & ( K != F )
        & ( K != G )
        & ( K != H )
        & ( K != I ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 )
      | ( X1 = X5 )
      | ( X1 = X6 )
      | ( X1 = X7 )
      | ( X1 = X8 )
      | ( X1 = X9 )
      | ( X1 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ B @ C ) )
     => ( B = C ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k1_tarski @ A )
          = ( k2_tarski @ B @ C ) )
       => ( B = C ) ) ),
    inference('cnf.neg',[status(esa)],[t9_zfmisc_1])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t63_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k6_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_xboole_0 @ ( k2_tarski @ X33 @ X34 ) @ ( k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t63_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ sk_B @ sk_C @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('5',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k6_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_xboole_0 @ ( k2_tarski @ X33 @ X34 ) @ ( k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t63_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X0 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ sk_B @ sk_C @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k6_enumset1 @ sk_A @ sk_A @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(t96_enumset1,axiom,(
    ! [A: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X44: $i] :
      ( ( k6_enumset1 @ X44 @ X44 @ X44 @ X44 @ X44 @ X44 @ X44 @ X44 )
      = ( k1_tarski @ X44 ) ) ),
    inference(cnf,[status(esa)],[t96_enumset1])).

thf('9',plain,
    ( ( k6_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 )
      | ( X1 = X5 )
      | ( X1 = X6 )
      | ( X1 = X7 )
      | ( X1 = X8 )
      | ( X1 = X9 )
      | ( X1 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k6_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t129_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k4_enumset1 @ D @ E @ F @ G @ H @ I ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k7_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X24 @ X25 @ X26 ) @ ( k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t129_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X1 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k6_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_xboole_0 @ ( k2_tarski @ X33 @ X34 ) @ ( k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t63_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X1 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 )
      = ( k6_enumset1 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i,J: $i] :
      ( ( J
        = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) )
    <=> ! [K: $i] :
          ( ( r2_hidden @ K @ J )
        <=> ~ ( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X11 @ X21 )
      | ( X21
       != ( k7_enumset1 @ X20 @ X19 @ X18 @ X17 @ X16 @ X15 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X11 @ ( k7_enumset1 @ X20 @ X19 @ X18 @ X17 @ X16 @ X15 @ X14 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X7 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( r2_hidden @ X0 @ ( k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X44: $i] :
      ( ( k6_enumset1 @ X44 @ X44 @ X44 @ X44 @ X44 @ X44 @ X44 @ X44 )
      = ( k1_tarski @ X44 ) ) ),
    inference(cnf,[status(esa)],[t96_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X1 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 )
      = ( k6_enumset1 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('26',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      | ( X21
       != ( k7_enumset1 @ X20 @ X19 @ X18 @ X17 @ X16 @ X15 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k7_enumset1 @ X20 @ X19 @ X18 @ X17 @ X16 @ X15 @ X14 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X7 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['31'])).

thf('34',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['31'])).

thf('35',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['31'])).

thf('36',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['31'])).

thf('37',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['31'])).

thf('38',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['31'])).

thf('39',plain,
    ( ( k6_enumset1 @ sk_B @ sk_C @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['9','32','33','34','35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X7 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X1 != X8 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( r2_hidden @ X1 @ ( k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    r2_hidden @ sk_C @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['39','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('46',plain,(
    ~ ( zip_tseitin_0 @ sk_C @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_C = sk_B )
    | ( sk_C = sk_B )
    | ( sk_C = sk_B )
    | ( sk_C = sk_B )
    | ( sk_C = sk_B )
    | ( sk_C = sk_B )
    | ( sk_C = sk_B )
    | ( sk_C = sk_B )
    | ( sk_C = sk_B ) ),
    inference('sup-',[status(thm)],['0','46'])).

thf('48',plain,(
    sk_C = sk_B ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o7zdtsnCcK
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:24:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 76 iterations in 0.075s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.54                                           $i > $i > $i).
% 0.20/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.20/0.54                                               $i > $i > $i > $i > $o).
% 0.20/0.54  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.54                                           $i > $i).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(d7_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i,J:$i]:
% 0.20/0.54     ( ( ( J ) = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) ) <=>
% 0.20/0.54       ( ![K:$i]:
% 0.20/0.54         ( ( r2_hidden @ K @ J ) <=>
% 0.20/0.54           ( ~( ( ( K ) != ( I ) ) & ( ( K ) != ( H ) ) & ( ( K ) != ( G ) ) & 
% 0.20/0.54                ( ( K ) != ( F ) ) & ( ( K ) != ( E ) ) & ( ( K ) != ( D ) ) & 
% 0.20/0.54                ( ( K ) != ( C ) ) & ( ( K ) != ( B ) ) & ( ( K ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, axiom,
% 0.20/0.54    (![K:$i,I:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.20/0.54       ( ( ( K ) != ( A ) ) & ( ( K ) != ( B ) ) & ( ( K ) != ( C ) ) & 
% 0.20/0.54         ( ( K ) != ( D ) ) & ( ( K ) != ( E ) ) & ( ( K ) != ( F ) ) & 
% 0.20/0.54         ( ( K ) != ( G ) ) & ( ( K ) != ( H ) ) & ( ( K ) != ( I ) ) ) ))).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, 
% 0.20/0.54         X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.20/0.54          | ((X1) = (X2))
% 0.20/0.54          | ((X1) = (X3))
% 0.20/0.54          | ((X1) = (X4))
% 0.20/0.54          | ((X1) = (X5))
% 0.20/0.54          | ((X1) = (X6))
% 0.20/0.54          | ((X1) = (X7))
% 0.20/0.54          | ((X1) = (X8))
% 0.20/0.54          | ((X1) = (X9))
% 0.20/0.54          | ((X1) = (X10)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t9_zfmisc_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( B ) = ( C ) ) ))).
% 0.20/0.54  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.54        ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( B ) = ( C ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t9_zfmisc_1])).
% 0.20/0.54  thf('1', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf(t63_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.54     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.54       ( k2_xboole_0 @
% 0.20/0.54         ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 0.20/0.54         X40 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X33 @ X34) @ 
% 0.20/0.54              (k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t63_enumset1])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         ((k6_enumset1 @ sk_B @ sk_C @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.20/0.54              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.54  thf(t69_enumset1, axiom,
% 0.20/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.54  thf('4', plain, (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 0.20/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 0.20/0.54         X40 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X33 @ X34) @ 
% 0.20/0.54              (k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t63_enumset1])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X0 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 0.20/0.54              (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         ((k6_enumset1 @ sk_B @ sk_C @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k6_enumset1 @ sk_A @ sk_A @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['3', '6'])).
% 0.20/0.54  thf(t96_enumset1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X44 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X44 @ X44 @ X44 @ X44 @ X44 @ X44 @ X44 @ X44)
% 0.20/0.54           = (k1_tarski @ X44))),
% 0.20/0.54      inference('cnf', [status(esa)], [t96_enumset1])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (((k6_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.54         = (k1_tarski @ sk_A))),
% 0.20/0.54      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, 
% 0.20/0.54         X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.20/0.54          | ((X1) = (X2))
% 0.20/0.54          | ((X1) = (X3))
% 0.20/0.54          | ((X1) = (X4))
% 0.20/0.54          | ((X1) = (X5))
% 0.20/0.54          | ((X1) = (X6))
% 0.20/0.54          | ((X1) = (X7))
% 0.20/0.54          | ((X1) = (X8))
% 0.20/0.54          | ((X1) = (X9))
% 0.20/0.54          | ((X1) = (X10)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (((k6_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.54         = (k1_tarski @ sk_A))),
% 0.20/0.54      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf(t70_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X42 : $i, X43 : $i]:
% 0.20/0.54         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 0.20/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.54  thf(t129_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.20/0.54     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.20/0.54       ( k2_xboole_0 @
% 0.20/0.54         ( k1_enumset1 @ A @ B @ C ) @ ( k4_enumset1 @ D @ E @ F @ G @ H @ I ) ) ))).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, 
% 0.20/0.54         X31 : $i, X32 : $i]:
% 0.20/0.54         ((k7_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 0.20/0.54           = (k2_xboole_0 @ (k1_enumset1 @ X24 @ X25 @ X26) @ 
% 0.20/0.54              (k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t129_enumset1])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k7_enumset1 @ X1 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 0.20/0.54              (k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 0.20/0.54         X40 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X33 @ X34) @ 
% 0.20/0.54              (k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t63_enumset1])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k7_enumset1 @ X1 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2)
% 0.20/0.54           = (k6_enumset1 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2))),
% 0.20/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.54  thf(zf_stmt_2, type, zip_tseitin_0 :
% 0.20/0.54      $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_3, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i,J:$i]:
% 0.20/0.54     ( ( ( J ) = ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) ) <=>
% 0.20/0.54       ( ![K:$i]:
% 0.20/0.54         ( ( r2_hidden @ K @ J ) <=>
% 0.20/0.54           ( ~( zip_tseitin_0 @ K @ I @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, 
% 0.20/0.54         X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ 
% 0.20/0.54           X19 @ X20)
% 0.20/0.54          | (r2_hidden @ X11 @ X21)
% 0.20/0.54          | ((X21)
% 0.20/0.54              != (k7_enumset1 @ X20 @ X19 @ X18 @ X17 @ X16 @ X15 @ X14 @ 
% 0.20/0.54                  X13 @ X12)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, 
% 0.20/0.54         X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.54         ((r2_hidden @ X11 @ 
% 0.20/0.54           (k7_enumset1 @ X20 @ X19 @ X18 @ X17 @ X16 @ X15 @ X14 @ X13 @ X12))
% 0.20/0.54          | (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ 
% 0.20/0.54             X19 @ X20))),
% 0.20/0.54      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.20/0.54         X7 : $i, X8 : $i]:
% 0.20/0.54         ((r2_hidden @ X8 @ 
% 0.20/0.54           (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.54          | (zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X7))),
% 0.20/0.54      inference('sup+', [status(thm)], ['16', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.20/0.54         X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         (((X1) != (X0))
% 0.20/0.54          | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, 
% 0.20/0.54         X8 : $i, X9 : $i]:
% 0.20/0.54         ~ (zip_tseitin_0 @ X0 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X0)),
% 0.20/0.54      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         (r2_hidden @ X0 @ 
% 0.20/0.54          (k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7))),
% 0.20/0.54      inference('sup-', [status(thm)], ['19', '21'])).
% 0.20/0.54  thf('23', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.54      inference('sup+', [status(thm)], ['11', '22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X44 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X44 @ X44 @ X44 @ X44 @ X44 @ X44 @ X44 @ X44)
% 0.20/0.54           = (k1_tarski @ X44))),
% 0.20/0.54      inference('cnf', [status(esa)], [t96_enumset1])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k7_enumset1 @ X1 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2)
% 0.20/0.54           = (k6_enumset1 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2))),
% 0.20/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, 
% 0.20/0.54         X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X22 @ X21)
% 0.20/0.54          | ~ (zip_tseitin_0 @ X22 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ 
% 0.20/0.54               X19 @ X20)
% 0.20/0.54          | ((X21)
% 0.20/0.54              != (k7_enumset1 @ X20 @ X19 @ X18 @ X17 @ X16 @ X15 @ X14 @ 
% 0.20/0.54                  X13 @ X12)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, 
% 0.20/0.54         X19 : $i, X20 : $i, X22 : $i]:
% 0.20/0.54         (~ (zip_tseitin_0 @ X22 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ 
% 0.20/0.54             X19 @ X20)
% 0.20/0.54          | ~ (r2_hidden @ X22 @ 
% 0.20/0.54               (k7_enumset1 @ X20 @ X19 @ X18 @ X17 @ X16 @ X15 @ X14 @ X13 @ 
% 0.20/0.54                X12)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.20/0.54         X7 : $i, X8 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X8 @ 
% 0.20/0.54             (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.54          | ~ (zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X7))),
% 0.20/0.54      inference('sup-', [status(thm)], ['25', '27'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.54          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['24', '28'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.20/0.54          sk_A @ sk_A @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '29'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      ((((sk_B) = (sk_A))
% 0.20/0.54        | ((sk_B) = (sk_A))
% 0.20/0.54        | ((sk_B) = (sk_A))
% 0.20/0.54        | ((sk_B) = (sk_A))
% 0.20/0.54        | ((sk_B) = (sk_A))
% 0.20/0.54        | ((sk_B) = (sk_A))
% 0.20/0.54        | ((sk_B) = (sk_A))
% 0.20/0.54        | ((sk_B) = (sk_A))
% 0.20/0.54        | ((sk_B) = (sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '30'])).
% 0.20/0.54  thf('32', plain, (((sk_B) = (sk_A))),
% 0.20/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.54  thf('33', plain, (((sk_B) = (sk_A))),
% 0.20/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.54  thf('34', plain, (((sk_B) = (sk_A))),
% 0.20/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.54  thf('35', plain, (((sk_B) = (sk_A))),
% 0.20/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.54  thf('36', plain, (((sk_B) = (sk_A))),
% 0.20/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.54  thf('37', plain, (((sk_B) = (sk_A))),
% 0.20/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.54  thf('38', plain, (((sk_B) = (sk_A))),
% 0.20/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (((k6_enumset1 @ sk_B @ sk_C @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B)
% 0.20/0.54         = (k1_tarski @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)],
% 0.20/0.54                ['9', '32', '33', '34', '35', '36', '37', '38'])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.20/0.54         X7 : $i, X8 : $i]:
% 0.20/0.54         ((r2_hidden @ X8 @ 
% 0.20/0.54           (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.54          | (zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X7))),
% 0.20/0.54      inference('sup+', [status(thm)], ['16', '18'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.20/0.54         X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         (((X1) != (X8))
% 0.20/0.54          | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, 
% 0.20/0.54         X8 : $i, X9 : $i]:
% 0.20/0.54         ~ (zip_tseitin_0 @ X8 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X0)),
% 0.20/0.54      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         (r2_hidden @ X1 @ 
% 0.20/0.54          (k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7))),
% 0.20/0.54      inference('sup-', [status(thm)], ['40', '42'])).
% 0.20/0.54  thf('44', plain, ((r2_hidden @ sk_C @ (k1_tarski @ sk_B))),
% 0.20/0.54      inference('sup+', [status(thm)], ['39', '43'])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.54          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['24', '28'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (~ (zip_tseitin_0 @ sk_C @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ 
% 0.20/0.54          sk_B @ sk_B @ sk_B)),
% 0.20/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      ((((sk_C) = (sk_B))
% 0.20/0.54        | ((sk_C) = (sk_B))
% 0.20/0.54        | ((sk_C) = (sk_B))
% 0.20/0.54        | ((sk_C) = (sk_B))
% 0.20/0.54        | ((sk_C) = (sk_B))
% 0.20/0.54        | ((sk_C) = (sk_B))
% 0.20/0.54        | ((sk_C) = (sk_B))
% 0.20/0.54        | ((sk_C) = (sk_B))
% 0.20/0.54        | ((sk_C) = (sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '46'])).
% 0.20/0.54  thf('48', plain, (((sk_C) = (sk_B))),
% 0.20/0.54      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.54  thf('49', plain, (((sk_B) != (sk_C))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf('50', plain, ($false),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
