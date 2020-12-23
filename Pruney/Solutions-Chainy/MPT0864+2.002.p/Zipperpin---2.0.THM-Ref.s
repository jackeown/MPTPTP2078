%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bpY4AmEey3

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:59 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 383 expanded)
%              Number of leaves         :   23 ( 113 expanded)
%              Depth                    :   20
%              Number of atoms          :  721 (3604 expanded)
%              Number of equality atoms :  121 ( 681 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X73: $i] :
      ( ( X73 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X73 ) @ X73 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X21 )
      | ( X23 = X22 )
      | ( X23 = X19 )
      | ( X21
       != ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X19: $i,X22: $i,X23: $i] :
      ( ( X23 = X19 )
      | ( X23 = X22 )
      | ~ ( r2_hidden @ X23 @ ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( ( k2_tarski @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('5',plain,(
    ! [X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X19 )
      | ( r2_hidden @ X20 @ X21 )
      | ( X21
       != ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('7',plain,(
    ! [X19: $i,X22: $i] :
      ( r2_hidden @ X19 @ ( k2_tarski @ X22 @ X19 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('10',plain,(
    ! [X70: $i,X71: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X70 @ X71 ) )
      = X70 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('11',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X70: $i,X72: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X70 @ X72 ) )
      = X72 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('14',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('18',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_2 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X73: $i,X74: $i,X75: $i] :
      ( ( X73 = k1_xboole_0 )
      | ~ ( r2_hidden @ X75 @ X73 )
      | ( ( sk_B @ X73 )
       != ( k4_tarski @ X75 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_A ) )
         != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','21'])).

thf('23',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X19: $i,X22: $i] :
      ( r2_hidden @ X19 @ ( k2_tarski @ X22 @ X19 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( r2_hidden @ X58 @ X59 )
      | ~ ( r1_tarski @ X59 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('32',plain,(
    ! [X19: $i,X22: $i] :
      ( r2_hidden @ X19 @ ( k2_tarski @ X22 @ X19 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('33',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('34',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('35',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['12','13'])).

thf('36',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X73: $i,X74: $i,X75: $i] :
      ( ( X73 = k1_xboole_0 )
      | ~ ( r2_hidden @ X74 @ X73 )
      | ( ( sk_B @ X73 )
       != ( k4_tarski @ X75 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_A ) )
         != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_A )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_A ) )
          = sk_A )
        | ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 )
        | ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf('42',plain,
    ( ( ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
        = sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_A ) )
         != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('44',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X19: $i,X22: $i] :
      ( r2_hidden @ X19 @ ( k2_tarski @ X22 @ X19 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('46',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('47',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k2_zfmisc_1 @ X56 @ X57 )
        = k1_xboole_0 )
      | ( X57 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('48',plain,(
    ! [X56: $i] :
      ( ( k2_zfmisc_1 @ X56 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('49',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( ( k1_mcart_1 @ X68 )
        = X67 )
      | ~ ( r2_hidden @ X68 @ ( k2_zfmisc_1 @ ( k1_tarski @ X67 ) @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( ( k1_mcart_1 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( k1_mcart_1 @ sk_A )
        = X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( k1_mcart_1 @ sk_A )
        = X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('53',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('55',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( r2_hidden @ X58 @ X59 )
      | ~ ( r1_tarski @ X59 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('56',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ X0 @ sk_A )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','57'])).

thf('59',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('60',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['28','60'])).

thf('62',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('63',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( ( k1_mcart_1 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( ( k1_mcart_1 @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( ( k1_mcart_1 @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( r1_tarski @ k1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['61','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bpY4AmEey3
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 401 iterations in 0.328s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.59/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.78  thf(sk_B_type, type, sk_B: $i > $i).
% 0.59/0.78  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.59/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.78  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.59/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.78  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.59/0.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.78  thf(t9_mcart_1, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.59/0.78          ( ![B:$i]:
% 0.59/0.78            ( ~( ( r2_hidden @ B @ A ) & 
% 0.59/0.78                 ( ![C:$i,D:$i]:
% 0.59/0.78                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.59/0.78                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.78  thf('0', plain,
% 0.59/0.78      (![X73 : $i]:
% 0.59/0.78         (((X73) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X73) @ X73))),
% 0.59/0.78      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.59/0.78  thf(d2_tarski, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.59/0.78       ( ![D:$i]:
% 0.59/0.78         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.59/0.78  thf('1', plain,
% 0.59/0.78      (![X19 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X23 @ X21)
% 0.59/0.78          | ((X23) = (X22))
% 0.59/0.78          | ((X23) = (X19))
% 0.59/0.78          | ((X21) != (k2_tarski @ X22 @ X19)))),
% 0.59/0.78      inference('cnf', [status(esa)], [d2_tarski])).
% 0.59/0.78  thf('2', plain,
% 0.59/0.78      (![X19 : $i, X22 : $i, X23 : $i]:
% 0.59/0.78         (((X23) = (X19))
% 0.59/0.78          | ((X23) = (X22))
% 0.59/0.78          | ~ (r2_hidden @ X23 @ (k2_tarski @ X22 @ X19)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['1'])).
% 0.59/0.78  thf('3', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 0.59/0.78          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 0.59/0.78          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['0', '2'])).
% 0.59/0.78  thf('4', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (((X0) != (X1))
% 0.59/0.78          | ((sk_B @ (k2_tarski @ X0 @ X1)) = (X1))
% 0.59/0.78          | ((k2_tarski @ X0 @ X1) = (k1_xboole_0)))),
% 0.59/0.78      inference('eq_fact', [status(thm)], ['3'])).
% 0.59/0.78  thf('5', plain,
% 0.59/0.78      (![X1 : $i]:
% 0.59/0.78         (((k2_tarski @ X1 @ X1) = (k1_xboole_0))
% 0.59/0.78          | ((sk_B @ (k2_tarski @ X1 @ X1)) = (X1)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['4'])).
% 0.59/0.78  thf('6', plain,
% 0.59/0.78      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.59/0.78         (((X20) != (X19))
% 0.59/0.78          | (r2_hidden @ X20 @ X21)
% 0.59/0.78          | ((X21) != (k2_tarski @ X22 @ X19)))),
% 0.59/0.78      inference('cnf', [status(esa)], [d2_tarski])).
% 0.59/0.78  thf('7', plain,
% 0.59/0.78      (![X19 : $i, X22 : $i]: (r2_hidden @ X19 @ (k2_tarski @ X22 @ X19))),
% 0.59/0.78      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.78  thf(t20_mcart_1, conjecture,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.59/0.78       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.78    (~( ![A:$i]:
% 0.59/0.78        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.59/0.78          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.59/0.78  thf('8', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_2))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('9', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_2))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(t7_mcart_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.59/0.78       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.59/0.78  thf('10', plain,
% 0.59/0.78      (![X70 : $i, X71 : $i]: ((k1_mcart_1 @ (k4_tarski @ X70 @ X71)) = (X70))),
% 0.59/0.78      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.59/0.78  thf('11', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.59/0.78      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.78  thf('12', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_2))),
% 0.59/0.78      inference('demod', [status(thm)], ['8', '11'])).
% 0.59/0.78  thf('13', plain,
% 0.59/0.78      (![X70 : $i, X72 : $i]: ((k2_mcart_1 @ (k4_tarski @ X70 @ X72)) = (X72))),
% 0.59/0.78      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.59/0.78  thf('14', plain, (((k2_mcart_1 @ sk_A) = (sk_C_2))),
% 0.59/0.78      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.78  thf('15', plain,
% 0.59/0.78      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('16', plain,
% 0.59/0.78      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('split', [status(esa)], ['15'])).
% 0.59/0.78  thf('17', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_2))),
% 0.59/0.78      inference('demod', [status(thm)], ['8', '11'])).
% 0.59/0.78  thf('18', plain,
% 0.59/0.78      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_2)))
% 0.59/0.78         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.78  thf('19', plain,
% 0.59/0.78      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 0.59/0.78         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup+', [status(thm)], ['14', '18'])).
% 0.59/0.78  thf('20', plain,
% 0.59/0.78      (![X73 : $i, X74 : $i, X75 : $i]:
% 0.59/0.78         (((X73) = (k1_xboole_0))
% 0.59/0.78          | ~ (r2_hidden @ X75 @ X73)
% 0.59/0.78          | ((sk_B @ X73) != (k4_tarski @ X75 @ X74)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.59/0.78  thf('21', plain,
% 0.59/0.78      ((![X0 : $i]:
% 0.59/0.78          (((sk_B @ X0) != (sk_A))
% 0.59/0.78           | ~ (r2_hidden @ sk_A @ X0)
% 0.59/0.78           | ((X0) = (k1_xboole_0))))
% 0.59/0.78         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.78  thf('22', plain,
% 0.59/0.78      ((![X0 : $i]:
% 0.59/0.78          (((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))
% 0.59/0.78           | ((sk_B @ (k2_tarski @ X0 @ sk_A)) != (sk_A))))
% 0.59/0.78         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['7', '21'])).
% 0.59/0.78  thf('23', plain,
% 0.59/0.78      (((((sk_A) != (sk_A))
% 0.59/0.78         | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 0.59/0.78         | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))))
% 0.59/0.78         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['5', '22'])).
% 0.59/0.78  thf('24', plain,
% 0.59/0.78      ((((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.59/0.78         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['23'])).
% 0.59/0.78  thf('25', plain,
% 0.59/0.78      (![X19 : $i, X22 : $i]: (r2_hidden @ X19 @ (k2_tarski @ X22 @ X19))),
% 0.59/0.78      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.78  thf(t7_ordinal1, axiom,
% 0.59/0.78    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.78  thf('26', plain,
% 0.59/0.78      (![X58 : $i, X59 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X58 @ X59) | ~ (r1_tarski @ X59 @ X58))),
% 0.59/0.78      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.59/0.78  thf('27', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X0)),
% 0.59/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.78  thf('28', plain,
% 0.59/0.78      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.59/0.78         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['24', '27'])).
% 0.59/0.78  thf(d10_xboole_0, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.78  thf('29', plain,
% 0.59/0.78      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.59/0.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.78  thf('30', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.59/0.78      inference('simplify', [status(thm)], ['29'])).
% 0.59/0.78  thf('31', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 0.59/0.78          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 0.59/0.78          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['0', '2'])).
% 0.59/0.78  thf('32', plain,
% 0.59/0.78      (![X19 : $i, X22 : $i]: (r2_hidden @ X19 @ (k2_tarski @ X22 @ X19))),
% 0.59/0.78      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.78  thf('33', plain,
% 0.59/0.78      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('split', [status(esa)], ['15'])).
% 0.59/0.78  thf('34', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_2))),
% 0.59/0.78      inference('demod', [status(thm)], ['8', '11'])).
% 0.59/0.78  thf('35', plain, (((k2_mcart_1 @ sk_A) = (sk_C_2))),
% 0.59/0.78      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.78  thf('36', plain,
% 0.59/0.78      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.59/0.78      inference('demod', [status(thm)], ['34', '35'])).
% 0.59/0.78  thf('37', plain,
% 0.59/0.78      ((((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_A)))
% 0.59/0.78         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup+', [status(thm)], ['33', '36'])).
% 0.59/0.78  thf('38', plain,
% 0.59/0.78      (![X73 : $i, X74 : $i, X75 : $i]:
% 0.59/0.78         (((X73) = (k1_xboole_0))
% 0.59/0.78          | ~ (r2_hidden @ X74 @ X73)
% 0.59/0.78          | ((sk_B @ X73) != (k4_tarski @ X75 @ X74)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.59/0.78  thf('39', plain,
% 0.59/0.78      ((![X0 : $i]:
% 0.59/0.78          (((sk_B @ X0) != (sk_A))
% 0.59/0.78           | ~ (r2_hidden @ sk_A @ X0)
% 0.59/0.78           | ((X0) = (k1_xboole_0))))
% 0.59/0.78         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['37', '38'])).
% 0.59/0.78  thf('40', plain,
% 0.59/0.78      ((![X0 : $i]:
% 0.59/0.78          (((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))
% 0.59/0.78           | ((sk_B @ (k2_tarski @ X0 @ sk_A)) != (sk_A))))
% 0.59/0.78         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['32', '39'])).
% 0.59/0.78  thf('41', plain,
% 0.59/0.78      ((![X0 : $i]:
% 0.59/0.78          (((X0) != (sk_A))
% 0.59/0.78           | ((sk_B @ (k2_tarski @ X0 @ sk_A)) = (sk_A))
% 0.59/0.78           | ((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))
% 0.59/0.78           | ((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))))
% 0.59/0.78         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['31', '40'])).
% 0.59/0.78  thf('42', plain,
% 0.59/0.78      (((((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 0.59/0.78         | ((sk_B @ (k2_tarski @ sk_A @ sk_A)) = (sk_A))))
% 0.59/0.78         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['41'])).
% 0.59/0.78  thf('43', plain,
% 0.59/0.78      ((![X0 : $i]:
% 0.59/0.78          (((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))
% 0.59/0.78           | ((sk_B @ (k2_tarski @ X0 @ sk_A)) != (sk_A))))
% 0.59/0.78         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['32', '39'])).
% 0.59/0.78  thf('44', plain,
% 0.59/0.78      ((((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.59/0.78         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('clc', [status(thm)], ['42', '43'])).
% 0.59/0.78  thf('45', plain,
% 0.59/0.78      (![X19 : $i, X22 : $i]: (r2_hidden @ X19 @ (k2_tarski @ X22 @ X19))),
% 0.59/0.78      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.78  thf('46', plain,
% 0.59/0.78      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup+', [status(thm)], ['44', '45'])).
% 0.59/0.78  thf(t113_zfmisc_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.59/0.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.78  thf('47', plain,
% 0.59/0.78      (![X56 : $i, X57 : $i]:
% 0.59/0.78         (((k2_zfmisc_1 @ X56 @ X57) = (k1_xboole_0))
% 0.59/0.78          | ((X57) != (k1_xboole_0)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.78  thf('48', plain,
% 0.59/0.78      (![X56 : $i]: ((k2_zfmisc_1 @ X56 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['47'])).
% 0.59/0.78  thf(t12_mcart_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.59/0.78       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.59/0.78         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.59/0.78  thf('49', plain,
% 0.59/0.78      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.59/0.78         (((k1_mcart_1 @ X68) = (X67))
% 0.59/0.78          | ~ (r2_hidden @ X68 @ (k2_zfmisc_1 @ (k1_tarski @ X67) @ X69)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.59/0.78  thf('50', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X1 @ k1_xboole_0) | ((k1_mcart_1 @ X1) = (X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.59/0.78  thf('51', plain,
% 0.59/0.78      ((![X0 : $i]: ((k1_mcart_1 @ sk_A) = (X0)))
% 0.59/0.78         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['46', '50'])).
% 0.59/0.78  thf('52', plain,
% 0.59/0.78      ((![X0 : $i]: ((k1_mcart_1 @ sk_A) = (X0)))
% 0.59/0.78         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['46', '50'])).
% 0.59/0.78  thf('53', plain,
% 0.59/0.78      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 0.59/0.78         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup+', [status(thm)], ['51', '52'])).
% 0.59/0.78  thf('54', plain,
% 0.59/0.78      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup+', [status(thm)], ['44', '45'])).
% 0.59/0.78  thf('55', plain,
% 0.59/0.78      (![X58 : $i, X59 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X58 @ X59) | ~ (r1_tarski @ X59 @ X58))),
% 0.59/0.78      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.59/0.78  thf('56', plain,
% 0.59/0.78      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.59/0.78         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['54', '55'])).
% 0.59/0.78  thf('57', plain,
% 0.59/0.78      ((![X0 : $i]: ~ (r1_tarski @ X0 @ sk_A))
% 0.59/0.78         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['53', '56'])).
% 0.59/0.78  thf('58', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['30', '57'])).
% 0.59/0.78  thf('59', plain,
% 0.59/0.78      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.59/0.78      inference('split', [status(esa)], ['15'])).
% 0.59/0.78  thf('60', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.59/0.78      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 0.59/0.78  thf('61', plain, (~ (r1_tarski @ k1_xboole_0 @ sk_A)),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['28', '60'])).
% 0.59/0.78  thf('62', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.59/0.78      inference('simplify', [status(thm)], ['29'])).
% 0.59/0.78  thf(d3_tarski, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.78       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.78  thf('63', plain,
% 0.59/0.78      (![X1 : $i, X3 : $i]:
% 0.59/0.78         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.78      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.78  thf('64', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X1 @ k1_xboole_0) | ((k1_mcart_1 @ X1) = (X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.59/0.78  thf('65', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((r1_tarski @ k1_xboole_0 @ X0)
% 0.59/0.78          | ((k1_mcart_1 @ (sk_C @ X0 @ k1_xboole_0)) = (X1)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['63', '64'])).
% 0.59/0.78  thf('66', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((r1_tarski @ k1_xboole_0 @ X0)
% 0.59/0.78          | ((k1_mcart_1 @ (sk_C @ X0 @ k1_xboole_0)) = (X1)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['63', '64'])).
% 0.59/0.78  thf('67', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         (((X0) = (X1))
% 0.59/0.78          | (r1_tarski @ k1_xboole_0 @ X2)
% 0.59/0.78          | (r1_tarski @ k1_xboole_0 @ X2))),
% 0.59/0.78      inference('sup+', [status(thm)], ['65', '66'])).
% 0.59/0.78  thf('68', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         ((r1_tarski @ k1_xboole_0 @ X2) | ((X0) = (X1)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['67'])).
% 0.59/0.78  thf('69', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X0)),
% 0.59/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.78  thf('70', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.59/0.78         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ k1_xboole_0 @ X3))),
% 0.59/0.78      inference('sup-', [status(thm)], ['68', '69'])).
% 0.59/0.78  thf('71', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.59/0.78      inference('sup-', [status(thm)], ['62', '70'])).
% 0.59/0.78  thf('72', plain, ($false), inference('demod', [status(thm)], ['61', '71'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
