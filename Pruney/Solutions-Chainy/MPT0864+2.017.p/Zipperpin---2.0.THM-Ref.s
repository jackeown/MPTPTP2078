%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Fn4MQaAPCL

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 161 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  774 (1378 expanded)
%              Number of equality atoms :  125 ( 232 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('0',plain,(
    ! [X43: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X43 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X34 ) )
        = ( k1_tarski @ X33 ) )
      | ( X33 = X34 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ( ( k4_xboole_0 @ X36 @ ( k1_tarski @ X35 ) )
       != X36 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33 != X32 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X32 ) )
       != ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('7',plain,(
    ! [X32: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X32 ) )
     != ( k1_tarski @ X32 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X32: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X32 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['5','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X17 @ X21 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['15'])).

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

thf('17',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('18',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X40 @ X41 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('19',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','21'])).

thf('23',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( r2_hidden @ X45 @ X43 )
      | ( ( sk_B @ X43 )
       != ( k4_tarski @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ sk_A @ X0 @ X1 @ X2 )
        | ( ( k1_enumset1 @ X2 @ X1 @ X0 )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
         != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
         != sk_A )
        | ( ( k1_enumset1 @ X1 @ X1 @ X0 )
          = k1_xboole_0 )
        | ( zip_tseitin_0 @ sk_A @ X0 @ X1 @ X1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('30',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
         != sk_A )
        | ( ( k2_tarski @ X1 @ X0 )
          = k1_xboole_0 )
        | ( zip_tseitin_0 @ sk_A @ X0 @ X1 @ X1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ ( k1_tarski @ X0 ) )
         != sk_A )
        | ( zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0 )
        | ( ( k2_tarski @ X0 @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','30'])).

thf('32',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ! [X32: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X32 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('34',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0 )
        | ( ( sk_B @ ( k1_tarski @ X0 ) )
         != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['31','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_A )
        | ( zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','35'])).

thf('37',plain,
    ( ( zip_tseitin_0 @ sk_A @ sk_A @ sk_A @ sk_A )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['5','11'])).

thf('39',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('42',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X40: $i,X42: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X40 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('44',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('46',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( r2_hidden @ X44 @ X43 )
      | ( ( sk_B @ X43 )
       != ( k4_tarski @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ sk_A @ X0 @ X1 @ X2 )
        | ( ( k1_enumset1 @ X2 @ X1 @ X0 )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
         != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
         != sk_A )
        | ( ( k1_enumset1 @ X1 @ X1 @ X0 )
          = k1_xboole_0 )
        | ( zip_tseitin_0 @ sk_A @ X0 @ X1 @ X1 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('54',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
         != sk_A )
        | ( ( k2_tarski @ X1 @ X0 )
          = k1_xboole_0 )
        | ( zip_tseitin_0 @ sk_A @ X0 @ X1 @ X1 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ ( k1_tarski @ X0 ) )
         != sk_A )
        | ( zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0 )
        | ( ( k2_tarski @ X0 @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0 )
        | ( ( sk_B @ ( k1_tarski @ X0 ) )
         != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_A )
        | ( zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','57'])).

thf('59',plain,
    ( ( zip_tseitin_0 @ sk_A @ sk_A @ sk_A @ sk_A )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('61',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('64',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('65',plain,(
    zip_tseitin_0 @ sk_A @ sk_A @ sk_A @ sk_A ),
    inference(simpl_trail,[status(thm)],['37','64'])).

thf('66',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('67',plain,(
    $false ),
    inference('sup-',[status(thm)],['65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Fn4MQaAPCL
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:19:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 115 iterations in 0.059s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(t9_mcart_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.53          ( ![B:$i]:
% 0.22/0.53            ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.53                 ( ![C:$i,D:$i]:
% 0.22/0.53                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.22/0.53                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (![X43 : $i]:
% 0.22/0.53         (((X43) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X43) @ X43))),
% 0.22/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.53  thf(t20_zfmisc_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.53         ( k1_tarski @ A ) ) <=>
% 0.22/0.53       ( ( A ) != ( B ) ) ))).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (![X33 : $i, X34 : $i]:
% 0.22/0.53         (((k4_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X34))
% 0.22/0.53            = (k1_tarski @ X33))
% 0.22/0.53          | ((X33) = (X34)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.53  thf(t65_zfmisc_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.22/0.53       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X35 : $i, X36 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X35 @ X36)
% 0.22/0.53          | ((k4_xboole_0 @ X36 @ (k1_tarski @ X35)) != (X36)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.22/0.53          | ((X0) = (X1))
% 0.22/0.53          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.53          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['0', '4'])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (![X32 : $i, X33 : $i]:
% 0.22/0.53         (((X33) != (X32))
% 0.22/0.53          | ((k4_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X32))
% 0.22/0.53              != (k1_tarski @ X33)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X32 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X32))
% 0.22/0.53           != (k1_tarski @ X32))),
% 0.22/0.53      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.53  thf(t1_boole, axiom,
% 0.22/0.53    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.53  thf('8', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.22/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.53  thf(t46_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X10 : $i, X11 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.53  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.53  thf('11', plain, (![X32 : $i]: ((k1_xboole_0) != (k1_tarski @ X32))),
% 0.22/0.53      inference('demod', [status(thm)], ['7', '10'])).
% 0.22/0.53  thf('12', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.22/0.53      inference('clc', [status(thm)], ['5', '11'])).
% 0.22/0.53  thf(t69_enumset1, axiom,
% 0.22/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.53  thf(t70_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X25 : $i, X26 : $i]:
% 0.22/0.53         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.22/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.53  thf(d1_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.53       ( ![E:$i]:
% 0.22/0.53         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.53           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.53  thf(zf_stmt_1, axiom,
% 0.22/0.53    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.53     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.53       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_2, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.53       ( ![E:$i]:
% 0.22/0.53         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.53         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.22/0.53          | (r2_hidden @ X17 @ X21)
% 0.22/0.53          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.53         ((r2_hidden @ X17 @ (k1_enumset1 @ X20 @ X19 @ X18))
% 0.22/0.53          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20))),
% 0.22/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.53  thf(t20_mcart_1, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.53       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_3, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.53          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.22/0.53  thf('17', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.53  thf(t7_mcart_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.22/0.53       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (![X40 : $i, X41 : $i]: ((k1_mcart_1 @ (k4_tarski @ X40 @ X41)) = (X40))),
% 0.22/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.53  thf('19', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('split', [status(esa)], ['20'])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['19', '21'])).
% 0.22/0.53  thf('23', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.22/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.22/0.53         (((X43) = (k1_xboole_0))
% 0.22/0.53          | ~ (r2_hidden @ X45 @ X43)
% 0.22/0.53          | ((sk_B @ X43) != (k4_tarski @ X45 @ X44)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          (((sk_B @ X0) != (sk_A))
% 0.22/0.53           | ~ (r2_hidden @ sk_A @ X0)
% 0.22/0.53           | ((X0) = (k1_xboole_0))))
% 0.22/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53          ((zip_tseitin_0 @ sk_A @ X0 @ X1 @ X2)
% 0.22/0.53           | ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.53           | ((sk_B @ (k1_enumset1 @ X2 @ X1 @ X0)) != (sk_A))))
% 0.22/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['16', '26'])).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      ((![X0 : $i, X1 : $i]:
% 0.22/0.53          (((sk_B @ (k2_tarski @ X1 @ X0)) != (sk_A))
% 0.22/0.53           | ((k1_enumset1 @ X1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.53           | (zip_tseitin_0 @ sk_A @ X0 @ X1 @ X1)))
% 0.22/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['14', '27'])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      (![X25 : $i, X26 : $i]:
% 0.22/0.53         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.22/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      ((![X0 : $i, X1 : $i]:
% 0.22/0.53          (((sk_B @ (k2_tarski @ X1 @ X0)) != (sk_A))
% 0.22/0.53           | ((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.53           | (zip_tseitin_0 @ sk_A @ X0 @ X1 @ X1)))
% 0.22/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          (((sk_B @ (k1_tarski @ X0)) != (sk_A))
% 0.22/0.53           | (zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0)
% 0.22/0.53           | ((k2_tarski @ X0 @ X0) = (k1_xboole_0))))
% 0.22/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['13', '30'])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.53  thf('33', plain, (![X32 : $i]: ((k1_xboole_0) != (k1_tarski @ X32))),
% 0.22/0.53      inference('demod', [status(thm)], ['7', '10'])).
% 0.22/0.53  thf('34', plain, (![X0 : $i]: ((k1_xboole_0) != (k2_tarski @ X0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          ((zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0)
% 0.22/0.53           | ((sk_B @ (k1_tarski @ X0)) != (sk_A))))
% 0.22/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('clc', [status(thm)], ['31', '34'])).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      ((![X0 : $i]: (((X0) != (sk_A)) | (zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0)))
% 0.22/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['12', '35'])).
% 0.22/0.53  thf('37', plain,
% 0.22/0.53      (((zip_tseitin_0 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.22/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.53  thf('38', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.22/0.53      inference('clc', [status(thm)], ['5', '11'])).
% 0.22/0.53  thf('39', plain,
% 0.22/0.53      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.53  thf('40', plain,
% 0.22/0.53      (![X25 : $i, X26 : $i]:
% 0.22/0.53         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.22/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.53  thf('41', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.53         ((r2_hidden @ X17 @ (k1_enumset1 @ X20 @ X19 @ X18))
% 0.22/0.53          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20))),
% 0.22/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.53  thf('42', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.53  thf('43', plain,
% 0.22/0.53      (![X40 : $i, X42 : $i]: ((k2_mcart_1 @ (k4_tarski @ X40 @ X42)) = (X42))),
% 0.22/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.53  thf('44', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.22/0.53      inference('sup+', [status(thm)], ['42', '43'])).
% 0.22/0.53  thf('45', plain,
% 0.22/0.53      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('split', [status(esa)], ['20'])).
% 0.22/0.53  thf('46', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['44', '45'])).
% 0.22/0.53  thf('47', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.53  thf('48', plain,
% 0.22/0.53      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.22/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['46', '47'])).
% 0.22/0.53  thf('49', plain,
% 0.22/0.53      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.22/0.53         (((X43) = (k1_xboole_0))
% 0.22/0.53          | ~ (r2_hidden @ X44 @ X43)
% 0.22/0.53          | ((sk_B @ X43) != (k4_tarski @ X45 @ X44)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.53  thf('50', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          (((sk_B @ X0) != (sk_A))
% 0.22/0.53           | ~ (r2_hidden @ sk_A @ X0)
% 0.22/0.53           | ((X0) = (k1_xboole_0))))
% 0.22/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.53  thf('51', plain,
% 0.22/0.53      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53          ((zip_tseitin_0 @ sk_A @ X0 @ X1 @ X2)
% 0.22/0.53           | ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.53           | ((sk_B @ (k1_enumset1 @ X2 @ X1 @ X0)) != (sk_A))))
% 0.22/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['41', '50'])).
% 0.22/0.53  thf('52', plain,
% 0.22/0.53      ((![X0 : $i, X1 : $i]:
% 0.22/0.53          (((sk_B @ (k2_tarski @ X1 @ X0)) != (sk_A))
% 0.22/0.53           | ((k1_enumset1 @ X1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.53           | (zip_tseitin_0 @ sk_A @ X0 @ X1 @ X1)))
% 0.22/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['40', '51'])).
% 0.22/0.53  thf('53', plain,
% 0.22/0.53      (![X25 : $i, X26 : $i]:
% 0.22/0.53         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.22/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.53  thf('54', plain,
% 0.22/0.53      ((![X0 : $i, X1 : $i]:
% 0.22/0.53          (((sk_B @ (k2_tarski @ X1 @ X0)) != (sk_A))
% 0.22/0.53           | ((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.53           | (zip_tseitin_0 @ sk_A @ X0 @ X1 @ X1)))
% 0.22/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('demod', [status(thm)], ['52', '53'])).
% 0.22/0.53  thf('55', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          (((sk_B @ (k1_tarski @ X0)) != (sk_A))
% 0.22/0.53           | (zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0)
% 0.22/0.53           | ((k2_tarski @ X0 @ X0) = (k1_xboole_0))))
% 0.22/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['39', '54'])).
% 0.22/0.53  thf('56', plain, (![X0 : $i]: ((k1_xboole_0) != (k2_tarski @ X0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.53  thf('57', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          ((zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0)
% 0.22/0.53           | ((sk_B @ (k1_tarski @ X0)) != (sk_A))))
% 0.22/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('clc', [status(thm)], ['55', '56'])).
% 0.22/0.53  thf('58', plain,
% 0.22/0.53      ((![X0 : $i]: (((X0) != (sk_A)) | (zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0)))
% 0.22/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['38', '57'])).
% 0.22/0.53  thf('59', plain,
% 0.22/0.53      (((zip_tseitin_0 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.22/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.53      inference('simplify', [status(thm)], ['58'])).
% 0.22/0.53  thf('60', plain,
% 0.22/0.53      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.53         (((X13) != (X12)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.53  thf('61', plain,
% 0.22/0.53      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.22/0.53         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X12)),
% 0.22/0.53      inference('simplify', [status(thm)], ['60'])).
% 0.22/0.53  thf('62', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['59', '61'])).
% 0.22/0.53  thf('63', plain,
% 0.22/0.53      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.53      inference('split', [status(esa)], ['20'])).
% 0.22/0.53  thf('64', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['62', '63'])).
% 0.22/0.53  thf('65', plain, ((zip_tseitin_0 @ sk_A @ sk_A @ sk_A @ sk_A)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['37', '64'])).
% 0.22/0.53  thf('66', plain,
% 0.22/0.53      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.22/0.53         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X12)),
% 0.22/0.53      inference('simplify', [status(thm)], ['60'])).
% 0.22/0.53  thf('67', plain, ($false), inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
