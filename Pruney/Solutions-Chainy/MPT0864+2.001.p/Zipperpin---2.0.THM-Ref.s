%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cCGkZkG14u

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:59 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 388 expanded)
%              Number of leaves         :   30 ( 117 expanded)
%              Depth                    :   20
%              Number of atoms          :  837 (3714 expanded)
%              Number of equality atoms :  138 ( 650 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k2_zfmisc_1 @ X56 @ X57 )
        = k1_xboole_0 )
      | ( X57 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X56: $i] :
      ( ( k2_zfmisc_1 @ X56 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('5',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( ( k1_mcart_1 @ X68 )
        = X67 )
      | ~ ( r2_hidden @ X68 @ ( k2_zfmisc_1 @ ( k1_tarski @ X67 ) @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( ( k1_mcart_1 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( ( k1_mcart_1 @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( ( k1_mcart_1 @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( r1_tarski @ k1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ( X8 = X9 )
      | ( X8 = X10 )
      | ( X8 = X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('12',plain,(
    ! [X73: $i] :
      ( ( X73 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X73 ) @ X73 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X13 @ X14 @ X15 )
      | ( X16
       != ( k1_enumset1 @ X15 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X13 @ X14 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_enumset1 @ X15 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_B @ ( k2_tarski @ X1 @ X0 ) ) @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( ( k2_tarski @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X0 @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X1 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( k2_tarski @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X19 )
      | ( r2_hidden @ X20 @ X21 )
      | ( X21
       != ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('23',plain,(
    ! [X19: $i,X22: $i] :
      ( r2_hidden @ X19 @ ( k2_tarski @ X22 @ X19 ) ) ),
    inference(simplify,[status(thm)],['22'])).

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

thf('24',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('26',plain,(
    ! [X70: $i,X71: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X70 @ X71 ) )
      = X70 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('27',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X70: $i,X72: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X70 @ X72 ) )
      = X72 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('30',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('34',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_2 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X73: $i,X74: $i,X75: $i] :
      ( ( X73 = k1_xboole_0 )
      | ~ ( r2_hidden @ X75 @ X73 )
      | ( ( sk_B @ X73 )
       != ( k4_tarski @ X75 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_A ) )
         != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','37'])).

thf('39',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','38'])).

thf('40',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X19: $i,X22: $i] :
      ( r2_hidden @ X19 @ ( k2_tarski @ X22 @ X19 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('42',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( r2_hidden @ X58 @ X59 )
      | ~ ( r1_tarski @ X59 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('47',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ X0 @ sk_A )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X0 @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X1 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('51',plain,(
    ! [X19: $i,X22: $i] :
      ( r2_hidden @ X19 @ ( k2_tarski @ X22 @ X19 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('52',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('53',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('54',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['28','29'])).

thf('55',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_A
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X73: $i,X74: $i,X75: $i] :
      ( ( X73 = k1_xboole_0 )
      | ~ ( r2_hidden @ X74 @ X73 )
      | ( ( sk_B @ X73 )
       != ( k4_tarski @ X75 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_A ) )
         != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( sk_A != sk_A )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_A ) )
          = X0 )
        | ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 )
        | ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_A ) )
          = X0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_A ) )
         != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_A )
        | ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 )
        | ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('66',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','66'])).

thf('68',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('69',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ X0 @ sk_A )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','69'])).

thf('71',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('72',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ X0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['47','72'])).

thf('74',plain,(
    $false ),
    inference('sup-',[status(thm)],['1','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cCGkZkG14u
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:08:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 305 iterations in 0.225s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.66  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.46/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.66  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.46/0.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(d10_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.66  thf('1', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.46/0.66      inference('simplify', [status(thm)], ['0'])).
% 0.46/0.66  thf(d3_tarski, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X1 : $i, X3 : $i]:
% 0.46/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.66  thf(t113_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X56 : $i, X57 : $i]:
% 0.46/0.66         (((k2_zfmisc_1 @ X56 @ X57) = (k1_xboole_0))
% 0.46/0.66          | ((X57) != (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (![X56 : $i]: ((k2_zfmisc_1 @ X56 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['3'])).
% 0.46/0.66  thf(t12_mcart_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.46/0.66       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.46/0.66         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.46/0.66         (((k1_mcart_1 @ X68) = (X67))
% 0.46/0.66          | ~ (r2_hidden @ X68 @ (k2_zfmisc_1 @ (k1_tarski @ X67) @ X69)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X1 @ k1_xboole_0) | ((k1_mcart_1 @ X1) = (X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r1_tarski @ k1_xboole_0 @ X0)
% 0.46/0.66          | ((k1_mcart_1 @ (sk_C @ X0 @ k1_xboole_0)) = (X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['2', '6'])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r1_tarski @ k1_xboole_0 @ X0)
% 0.46/0.66          | ((k1_mcart_1 @ (sk_C @ X0 @ k1_xboole_0)) = (X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['2', '6'])).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (((X0) = (X1))
% 0.46/0.66          | (r1_tarski @ k1_xboole_0 @ X2)
% 0.46/0.66          | (r1_tarski @ k1_xboole_0 @ X2))),
% 0.46/0.66      inference('sup+', [status(thm)], ['7', '8'])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((r1_tarski @ k1_xboole_0 @ X2) | ((X0) = (X1)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.66  thf(d1_enumset1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.66       ( ![E:$i]:
% 0.46/0.66         ( ( r2_hidden @ E @ D ) <=>
% 0.46/0.66           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, axiom,
% 0.46/0.66    (![E:$i,C:$i,B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.46/0.66       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11)
% 0.46/0.66          | ((X8) = (X9))
% 0.46/0.66          | ((X8) = (X10))
% 0.46/0.66          | ((X8) = (X11)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t9_mcart_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.66          ( ![B:$i]:
% 0.46/0.66            ( ~( ( r2_hidden @ B @ A ) & 
% 0.46/0.66                 ( ![C:$i,D:$i]:
% 0.46/0.66                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.46/0.66                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X73 : $i]:
% 0.46/0.66         (((X73) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X73) @ X73))),
% 0.46/0.66      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.46/0.66  thf(t70_enumset1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X25 : $i, X26 : $i]:
% 0.46/0.66         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.46/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.66  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_2, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.66       ( ![E:$i]:
% 0.46/0.66         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X17 @ X16)
% 0.46/0.66          | ~ (zip_tseitin_0 @ X17 @ X13 @ X14 @ X15)
% 0.46/0.66          | ((X16) != (k1_enumset1 @ X15 @ X14 @ X13)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 0.46/0.66         (~ (zip_tseitin_0 @ X17 @ X13 @ X14 @ X15)
% 0.46/0.66          | ~ (r2_hidden @ X17 @ (k1_enumset1 @ X15 @ X14 @ X13)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['14'])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.66          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['13', '15'])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.66          | ~ (zip_tseitin_0 @ (sk_B @ (k2_tarski @ X1 @ X0)) @ X0 @ X1 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['12', '16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((sk_B @ (k2_tarski @ X0 @ X1)) = (X0))
% 0.46/0.66          | ((sk_B @ (k2_tarski @ X0 @ X1)) = (X0))
% 0.46/0.66          | ((sk_B @ (k2_tarski @ X0 @ X1)) = (X1))
% 0.46/0.66          | ((k2_tarski @ X0 @ X1) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '17'])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_tarski @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.66          | ((sk_B @ (k2_tarski @ X0 @ X1)) = (X1))
% 0.46/0.66          | ((sk_B @ (k2_tarski @ X0 @ X1)) = (X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X0) != (X1))
% 0.46/0.66          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 0.46/0.66          | ((k2_tarski @ X1 @ X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('eq_fact', [status(thm)], ['19'])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X1 : $i]:
% 0.46/0.66         (((k2_tarski @ X1 @ X1) = (k1_xboole_0))
% 0.46/0.66          | ((sk_B @ (k2_tarski @ X1 @ X1)) = (X1)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.66  thf(d2_tarski, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.46/0.66       ( ![D:$i]:
% 0.46/0.66         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.66         (((X20) != (X19))
% 0.46/0.66          | (r2_hidden @ X20 @ X21)
% 0.46/0.66          | ((X21) != (k2_tarski @ X22 @ X19)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d2_tarski])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X19 : $i, X22 : $i]: (r2_hidden @ X19 @ (k2_tarski @ X22 @ X19))),
% 0.46/0.66      inference('simplify', [status(thm)], ['22'])).
% 0.46/0.66  thf(t20_mcart_1, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.46/0.66       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_3, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.46/0.66          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.46/0.66  thf('24', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_2))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf('25', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_2))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf(t7_mcart_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.46/0.66       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X70 : $i, X71 : $i]: ((k1_mcart_1 @ (k4_tarski @ X70 @ X71)) = (X70))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.46/0.66  thf('27', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['25', '26'])).
% 0.46/0.66  thf('28', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_2))),
% 0.46/0.66      inference('demod', [status(thm)], ['24', '27'])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X70 : $i, X72 : $i]: ((k2_mcart_1 @ (k4_tarski @ X70 @ X72)) = (X72))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.46/0.66  thf('30', plain, (((k2_mcart_1 @ sk_A) = (sk_C_2))),
% 0.46/0.66      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('split', [status(esa)], ['31'])).
% 0.46/0.66  thf('33', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_2))),
% 0.46/0.66      inference('demod', [status(thm)], ['24', '27'])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_2)))
% 0.46/0.66         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['32', '33'])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 0.46/0.66         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['30', '34'])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (![X73 : $i, X74 : $i, X75 : $i]:
% 0.46/0.66         (((X73) = (k1_xboole_0))
% 0.46/0.66          | ~ (r2_hidden @ X75 @ X73)
% 0.46/0.66          | ((sk_B @ X73) != (k4_tarski @ X75 @ X74)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          (((sk_B @ X0) != (sk_A))
% 0.46/0.66           | ~ (r2_hidden @ sk_A @ X0)
% 0.46/0.66           | ((X0) = (k1_xboole_0))))
% 0.46/0.66         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          (((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))
% 0.46/0.66           | ((sk_B @ (k2_tarski @ X0 @ sk_A)) != (sk_A))))
% 0.46/0.66         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['23', '37'])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (((((sk_A) != (sk_A))
% 0.46/0.66         | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 0.46/0.66         | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))))
% 0.46/0.66         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['21', '38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      ((((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.46/0.66         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (![X19 : $i, X22 : $i]: (r2_hidden @ X19 @ (k2_tarski @ X22 @ X19))),
% 0.46/0.66      inference('simplify', [status(thm)], ['22'])).
% 0.46/0.66  thf(t7_ordinal1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X58 : $i, X59 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X58 @ X59) | ~ (r1_tarski @ X59 @ X58))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.46/0.66         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['40', '43'])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 0.46/0.66         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['10', '44'])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.46/0.66         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['40', '43'])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      ((![X0 : $i]: ~ (r1_tarski @ X0 @ sk_A))
% 0.46/0.66         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.66  thf('48', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.46/0.66      inference('simplify', [status(thm)], ['0'])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((r1_tarski @ k1_xboole_0 @ X2) | ((X0) = (X1)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_tarski @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.66          | ((sk_B @ (k2_tarski @ X0 @ X1)) = (X1))
% 0.46/0.66          | ((sk_B @ (k2_tarski @ X0 @ X1)) = (X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X19 : $i, X22 : $i]: (r2_hidden @ X19 @ (k2_tarski @ X22 @ X19))),
% 0.46/0.66      inference('simplify', [status(thm)], ['22'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('split', [status(esa)], ['31'])).
% 0.46/0.66  thf('53', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_2))),
% 0.46/0.66      inference('demod', [status(thm)], ['24', '27'])).
% 0.46/0.66  thf('54', plain, (((k2_mcart_1 @ sk_A) = (sk_C_2))),
% 0.46/0.66      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      ((((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_A)))
% 0.46/0.66         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['52', '55'])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (![X73 : $i, X74 : $i, X75 : $i]:
% 0.46/0.66         (((X73) = (k1_xboole_0))
% 0.46/0.66          | ~ (r2_hidden @ X74 @ X73)
% 0.46/0.66          | ((sk_B @ X73) != (k4_tarski @ X75 @ X74)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          (((sk_B @ X0) != (sk_A))
% 0.46/0.66           | ~ (r2_hidden @ sk_A @ X0)
% 0.46/0.66           | ((X0) = (k1_xboole_0))))
% 0.46/0.66         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          (((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))
% 0.46/0.66           | ((sk_B @ (k2_tarski @ X0 @ sk_A)) != (sk_A))))
% 0.46/0.66         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['51', '58'])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          (((sk_A) != (sk_A))
% 0.46/0.66           | ((sk_B @ (k2_tarski @ X0 @ sk_A)) = (X0))
% 0.46/0.66           | ((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))
% 0.46/0.66           | ((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))))
% 0.46/0.66         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['50', '59'])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          (((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))
% 0.46/0.66           | ((sk_B @ (k2_tarski @ X0 @ sk_A)) = (X0))))
% 0.46/0.66         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['60'])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          (((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))
% 0.46/0.66           | ((sk_B @ (k2_tarski @ X0 @ sk_A)) != (sk_A))))
% 0.46/0.66         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['51', '58'])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          (((X0) != (sk_A))
% 0.46/0.66           | ((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))
% 0.46/0.66           | ((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))))
% 0.46/0.66         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      ((((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.46/0.66         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['63'])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.46/0.66         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['64', '65'])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 0.46/0.66         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['49', '66'])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.46/0.66         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['64', '65'])).
% 0.46/0.66  thf('69', plain,
% 0.46/0.66      ((![X0 : $i]: ~ (r1_tarski @ X0 @ sk_A))
% 0.46/0.66         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.66  thf('70', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['48', '69'])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['31'])).
% 0.46/0.66  thf('72', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.46/0.66  thf('73', plain, (![X0 : $i]: ~ (r1_tarski @ X0 @ sk_A)),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['47', '72'])).
% 0.46/0.66  thf('74', plain, ($false), inference('sup-', [status(thm)], ['1', '73'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
