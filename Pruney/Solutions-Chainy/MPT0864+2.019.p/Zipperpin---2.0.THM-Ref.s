%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kzxXBhvQK8

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:01 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 819 expanded)
%              Number of leaves         :   26 ( 227 expanded)
%              Depth                    :   19
%              Number of atoms          :  757 (7508 expanded)
%              Number of equality atoms :  123 (1454 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X5 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('1',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X5 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('8',plain,(
    ! [X38: $i,X40: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X38 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('9',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_2 @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_2 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_2 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_zfmisc_1 @ X23 @ X24 )
        = k1_xboole_0 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X24: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X24 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ ( k2_zfmisc_1 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ k1_xboole_0 )
      | ( r2_hidden @ X2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ~ ( r2_hidden @ sk_A @ k1_xboole_0 )
      | ( r2_hidden @ sk_B_2 @ k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

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

thf('18',plain,(
    ! [X41: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X41 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('20',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_2 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('25',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( r2_hidden @ X42 @ X41 )
      | ( ( sk_B_1 @ X41 )
       != ( k4_tarski @ X43 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B_1 @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_B_2 @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','31'])).

thf('33',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('34',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B_2 = sk_A )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','36'])).

thf('38',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_zfmisc_1 @ X23 @ X24 )
        = k1_xboole_0 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X23: $i] :
      ( ( k2_zfmisc_1 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ ( k2_zfmisc_1 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ k1_xboole_0 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ k1_xboole_0 )
        | ( r2_hidden @ sk_A @ X0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('45',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( sk_B @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X23: $i] :
      ( ( k2_zfmisc_1 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('49',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X38 @ X39 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('51',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_2 ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('53',plain,
    ( ( sk_A = sk_B_2 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_2 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_2 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('57',plain,(
    ! [X38: $i,X40: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X38 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('58',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C_2 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ ( k2_zfmisc_1 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('61',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
        | ( r2_hidden @ sk_A @ X1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ k1_xboole_0 )
        | ( r2_hidden @ sk_A @ X0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('64',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('65',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( r2_hidden @ X43 @ X41 )
      | ( ( sk_B_1 @ X41 )
       != ( k4_tarski @ X43 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B_1 @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('69',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('71',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ X0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','71'])).

thf('73',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('74',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ X0 @ sk_A )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','74'])).

thf('76',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('77',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(simpl_trail,[status(thm)],['44','77'])).

thf('79',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('80',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['3','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('83',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('84',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['81','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kzxXBhvQK8
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 326 iterations in 0.141s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.38/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.60  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.38/0.60  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.38/0.60  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.38/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.38/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.60  thf(d2_tarski, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.38/0.60       ( ![D:$i]:
% 0.38/0.60         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.60         (((X6) != (X5))
% 0.38/0.60          | (r2_hidden @ X6 @ X7)
% 0.38/0.60          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d2_tarski])).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      (![X5 : $i, X8 : $i]: (r2_hidden @ X5 @ (k2_tarski @ X8 @ X5))),
% 0.38/0.60      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.60  thf(t7_ordinal1, axiom,
% 0.38/0.60    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (![X29 : $i, X30 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 0.38/0.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]: ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X0)),
% 0.38/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.60  thf(t20_mcart_1, conjecture,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.38/0.60       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i]:
% 0.38/0.60        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.38/0.60          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('split', [status(esa)], ['4'])).
% 0.38/0.60  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B_2 @ sk_C_2))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('7', plain, (((sk_A) = (k4_tarski @ sk_B_2 @ sk_C_2))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(t7_mcart_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.38/0.60       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      (![X38 : $i, X40 : $i]: ((k2_mcart_1 @ (k4_tarski @ X38 @ X40)) = (X40))),
% 0.38/0.60      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.38/0.60  thf('9', plain, (((k2_mcart_1 @ sk_A) = (sk_C_2))),
% 0.38/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.60  thf('10', plain, (((sk_A) = (k4_tarski @ sk_B_2 @ (k2_mcart_1 @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['6', '9'])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      ((((sk_A) = (k4_tarski @ sk_B_2 @ sk_A)))
% 0.38/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['5', '10'])).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      ((((sk_A) = (k4_tarski @ sk_B_2 @ sk_A)))
% 0.38/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['5', '10'])).
% 0.38/0.60  thf(t113_zfmisc_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      (![X23 : $i, X24 : $i]:
% 0.38/0.60         (((k2_zfmisc_1 @ X23 @ X24) = (k1_xboole_0))
% 0.38/0.60          | ((X23) != (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      (![X24 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X24) = (k1_xboole_0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['13'])).
% 0.38/0.60  thf(l54_zfmisc_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.38/0.60       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.60         ((r2_hidden @ X17 @ X18)
% 0.38/0.60          | ~ (r2_hidden @ (k4_tarski @ X17 @ X19) @ (k2_zfmisc_1 @ X18 @ X20)))),
% 0.38/0.60      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (![X1 : $i, X2 : $i]:
% 0.38/0.60         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ k1_xboole_0)
% 0.38/0.60          | (r2_hidden @ X2 @ k1_xboole_0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      (((~ (r2_hidden @ sk_A @ k1_xboole_0)
% 0.38/0.60         | (r2_hidden @ sk_B_2 @ k1_xboole_0)))
% 0.38/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['12', '16'])).
% 0.38/0.60  thf(t9_mcart_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.60          ( ![B:$i]:
% 0.38/0.60            ( ~( ( r2_hidden @ B @ A ) & 
% 0.38/0.60                 ( ![C:$i,D:$i]:
% 0.38/0.60                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.38/0.60                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      (![X41 : $i]:
% 0.38/0.60         (((X41) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X41) @ X41))),
% 0.38/0.60      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.38/0.60  thf(d1_tarski, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.60  thf('20', plain,
% 0.38/0.60      (![X0 : $i, X3 : $i]:
% 0.38/0.60         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.60          | ((sk_B_1 @ (k1_tarski @ X0)) = (X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['18', '20'])).
% 0.38/0.60  thf('22', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.60  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      ((((sk_A) = (k4_tarski @ sk_B_2 @ sk_A)))
% 0.38/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['5', '10'])).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.38/0.60         (((X41) = (k1_xboole_0))
% 0.38/0.60          | ~ (r2_hidden @ X42 @ X41)
% 0.38/0.60          | ((sk_B_1 @ X41) != (k4_tarski @ X43 @ X42)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          (((sk_B_1 @ X0) != (sk_A))
% 0.38/0.60           | ~ (r2_hidden @ sk_A @ X0)
% 0.38/0.60           | ((X0) = (k1_xboole_0))))
% 0.38/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.38/0.60         | ((sk_B_1 @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.38/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['23', '26'])).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      (((((sk_A) != (sk_A))
% 0.38/0.60         | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.38/0.60         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.38/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['21', '27'])).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.38/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['28'])).
% 0.38/0.60  thf('30', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.38/0.60  thf('31', plain,
% 0.38/0.60      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['29', '30'])).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      (((r2_hidden @ sk_B_2 @ k1_xboole_0))
% 0.38/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('demod', [status(thm)], ['17', '31'])).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.38/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['28'])).
% 0.38/0.60  thf('34', plain,
% 0.38/0.60      (![X0 : $i, X3 : $i]:
% 0.38/0.60         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.38/0.60  thf('35', plain,
% 0.38/0.60      ((![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | ((X0) = (sk_A))))
% 0.38/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.60  thf('36', plain,
% 0.38/0.60      ((((sk_B_2) = (sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['32', '35'])).
% 0.38/0.60  thf('37', plain,
% 0.38/0.60      ((((sk_A) = (k4_tarski @ sk_A @ sk_A)))
% 0.38/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('demod', [status(thm)], ['11', '36'])).
% 0.38/0.60  thf('38', plain,
% 0.38/0.60      (![X23 : $i, X24 : $i]:
% 0.38/0.60         (((k2_zfmisc_1 @ X23 @ X24) = (k1_xboole_0))
% 0.38/0.60          | ((X24) != (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.60  thf('39', plain,
% 0.38/0.60      (![X23 : $i]: ((k2_zfmisc_1 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.38/0.60  thf('40', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.60         ((r2_hidden @ X17 @ X18)
% 0.38/0.60          | ~ (r2_hidden @ (k4_tarski @ X17 @ X19) @ (k2_zfmisc_1 @ X18 @ X20)))),
% 0.38/0.60      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.38/0.60  thf('41', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ k1_xboole_0)
% 0.38/0.60          | (r2_hidden @ X2 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.60  thf('42', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          (~ (r2_hidden @ sk_A @ k1_xboole_0) | (r2_hidden @ sk_A @ X0)))
% 0.38/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['37', '41'])).
% 0.38/0.60  thf('43', plain,
% 0.38/0.60      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['29', '30'])).
% 0.38/0.60  thf('44', plain,
% 0.38/0.60      ((![X0 : $i]: (r2_hidden @ sk_A @ X0))
% 0.38/0.60         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('demod', [status(thm)], ['42', '43'])).
% 0.38/0.60  thf(existence_m1_subset_1, axiom,
% 0.38/0.60    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.38/0.60  thf('45', plain, (![X25 : $i]: (m1_subset_1 @ (sk_B @ X25) @ X25)),
% 0.38/0.60      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.38/0.60  thf(t3_subset, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.60  thf('46', plain,
% 0.38/0.60      (![X26 : $i, X27 : $i]:
% 0.38/0.60         ((r1_tarski @ X26 @ X27) | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.60  thf('47', plain,
% 0.38/0.60      (![X0 : $i]: (r1_tarski @ (sk_B @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.38/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.60  thf('48', plain,
% 0.38/0.60      (![X23 : $i]: ((k2_zfmisc_1 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.38/0.60  thf('49', plain, (((sk_A) = (k4_tarski @ sk_B_2 @ sk_C_2))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('50', plain,
% 0.38/0.60      (![X38 : $i, X39 : $i]: ((k1_mcart_1 @ (k4_tarski @ X38 @ X39)) = (X38))),
% 0.38/0.60      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.38/0.60  thf('51', plain, (((k1_mcart_1 @ sk_A) = (sk_B_2))),
% 0.38/0.60      inference('sup+', [status(thm)], ['49', '50'])).
% 0.38/0.60  thf('52', plain,
% 0.38/0.60      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('split', [status(esa)], ['4'])).
% 0.38/0.60  thf('53', plain,
% 0.38/0.60      ((((sk_A) = (sk_B_2))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['51', '52'])).
% 0.38/0.60  thf('54', plain, (((sk_A) = (k4_tarski @ sk_B_2 @ sk_C_2))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('55', plain,
% 0.38/0.60      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_2)))
% 0.38/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['53', '54'])).
% 0.38/0.60  thf('56', plain,
% 0.38/0.60      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_2)))
% 0.38/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['53', '54'])).
% 0.38/0.60  thf('57', plain,
% 0.38/0.60      (![X38 : $i, X40 : $i]: ((k2_mcart_1 @ (k4_tarski @ X38 @ X40)) = (X40))),
% 0.38/0.60      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.38/0.60  thf('58', plain,
% 0.38/0.60      ((((k2_mcart_1 @ sk_A) = (sk_C_2))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['56', '57'])).
% 0.38/0.60  thf('59', plain,
% 0.38/0.60      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 0.38/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('demod', [status(thm)], ['55', '58'])).
% 0.38/0.60  thf('60', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.60         ((r2_hidden @ X17 @ X18)
% 0.38/0.60          | ~ (r2_hidden @ (k4_tarski @ X17 @ X19) @ (k2_zfmisc_1 @ X18 @ X20)))),
% 0.38/0.60      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.38/0.60  thf('61', plain,
% 0.38/0.60      ((![X0 : $i, X1 : $i]:
% 0.38/0.60          (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.38/0.60           | (r2_hidden @ sk_A @ X1)))
% 0.38/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.60  thf('62', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          (~ (r2_hidden @ sk_A @ k1_xboole_0) | (r2_hidden @ sk_A @ X0)))
% 0.38/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['48', '61'])).
% 0.38/0.60  thf('63', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.38/0.60  thf('64', plain,
% 0.38/0.60      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 0.38/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('demod', [status(thm)], ['55', '58'])).
% 0.38/0.60  thf('65', plain,
% 0.38/0.60      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.38/0.60         (((X41) = (k1_xboole_0))
% 0.38/0.60          | ~ (r2_hidden @ X43 @ X41)
% 0.38/0.60          | ((sk_B_1 @ X41) != (k4_tarski @ X43 @ X42)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.38/0.60  thf('66', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          (((sk_B_1 @ X0) != (sk_A))
% 0.38/0.60           | ~ (r2_hidden @ sk_A @ X0)
% 0.38/0.60           | ((X0) = (k1_xboole_0))))
% 0.38/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['64', '65'])).
% 0.38/0.60  thf('67', plain,
% 0.38/0.60      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.38/0.60         | ((sk_B_1 @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.38/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['63', '66'])).
% 0.38/0.60  thf('68', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.60          | ((sk_B_1 @ (k1_tarski @ X0)) = (X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['18', '20'])).
% 0.38/0.60  thf('69', plain,
% 0.38/0.60      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.38/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('clc', [status(thm)], ['67', '68'])).
% 0.38/0.60  thf('70', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.38/0.60  thf('71', plain,
% 0.38/0.60      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['69', '70'])).
% 0.38/0.60  thf('72', plain,
% 0.38/0.60      ((![X0 : $i]: (r2_hidden @ sk_A @ X0))
% 0.38/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('demod', [status(thm)], ['62', '71'])).
% 0.38/0.60  thf('73', plain,
% 0.38/0.60      (![X29 : $i, X30 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 0.38/0.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.60  thf('74', plain,
% 0.38/0.60      ((![X0 : $i]: ~ (r1_tarski @ X0 @ sk_A))
% 0.38/0.60         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['72', '73'])).
% 0.38/0.60  thf('75', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['47', '74'])).
% 0.38/0.60  thf('76', plain,
% 0.38/0.60      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.38/0.60      inference('split', [status(esa)], ['4'])).
% 0.38/0.60  thf('77', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.38/0.60      inference('sat_resolution*', [status(thm)], ['75', '76'])).
% 0.38/0.60  thf('78', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.38/0.60      inference('simpl_trail', [status(thm)], ['44', '77'])).
% 0.38/0.60  thf('79', plain,
% 0.38/0.60      (![X0 : $i, X3 : $i]:
% 0.38/0.60         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.38/0.60  thf('80', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['78', '79'])).
% 0.38/0.60  thf('81', plain, (![X0 : $i]: ~ (r1_tarski @ sk_A @ X0)),
% 0.38/0.60      inference('demod', [status(thm)], ['3', '80'])).
% 0.38/0.60  thf('82', plain,
% 0.38/0.60      (![X0 : $i]: (r1_tarski @ (sk_B @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.38/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.60  thf('83', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['78', '79'])).
% 0.38/0.60  thf('84', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['78', '79'])).
% 0.38/0.60  thf('85', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.38/0.60      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.38/0.60  thf('86', plain, ($false), inference('demod', [status(thm)], ['81', '85'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
