%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7f9S5FaEiu

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 318 expanded)
%              Number of leaves         :   21 (  95 expanded)
%              Depth                    :   16
%              Number of atoms          :  697 (2894 expanded)
%              Number of equality atoms :  112 ( 521 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X16 != X15 )
      | ( r2_hidden @ X16 @ X17 )
      | ( X17
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X15: $i] :
      ( r2_hidden @ X15 @ ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['10'])).

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

thf('12',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('16',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X26 @ X27 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('17',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('20',plain,(
    ! [X26: $i,X28: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X26 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( r2_hidden @ X31 @ X29 )
      | ( ( sk_B @ X29 )
       != ( k4_tarski @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','25'])).

thf('27',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('28',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( X18 = X15 )
      | ( X17
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('29',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18 = X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['26','30'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('33',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( ( k4_xboole_0 @ X24 @ ( k1_tarski @ X23 ) )
       != X24 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
       != ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X15: $i] :
      ( r2_hidden @ X15 @ ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
       != ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['26','30'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
       != ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_xboole_0
     != ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','42'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('44',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( $false
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('48',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('49',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('50',plain,
    ( ( sk_A
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('52',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( r2_hidden @ X30 @ X29 )
      | ( ( sk_B @ X29 )
       != ( k4_tarski @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k4_tarski @ X2 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    ! [X15: $i] :
      ( r2_hidden @ X15 @ ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('57',plain,
    ( ( sk_A
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('58',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','38'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
       != ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
       != ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_xboole_0
     != ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','62'])).

thf('64',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('68',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['46','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7f9S5FaEiu
% 0.11/0.34  % Computer   : n014.cluster.edu
% 0.11/0.34  % Model      : x86_64 x86_64
% 0.11/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.34  % Memory     : 8042.1875MB
% 0.11/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.34  % CPULimit   : 60
% 0.11/0.34  % DateTime   : Tue Dec  1 15:10:52 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.11/0.34  % Running portfolio for 600 s
% 0.11/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.34  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 256 iterations in 0.134s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.55  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.55  thf(t9_mcart_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.55                 ( ![C:$i,D:$i]:
% 0.20/0.55                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.55                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X29 : $i]:
% 0.20/0.55         (((X29) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X29) @ X29))),
% 0.20/0.55      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.55  thf(d5_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.55       ( ![D:$i]:
% 0.20/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.55          | (r2_hidden @ X10 @ X7)
% 0.20/0.55          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.55         ((r2_hidden @ X10 @ X7)
% 0.20/0.55          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.55          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '2'])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X29 : $i]:
% 0.20/0.55         (((X29) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X29) @ X29))),
% 0.20/0.55      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.55          | ~ (r2_hidden @ X10 @ X8)
% 0.20/0.55          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X10 @ X8)
% 0.20/0.55          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.20/0.55          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.55  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.55  thf(d1_tarski, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.55         (((X16) != (X15))
% 0.20/0.55          | (r2_hidden @ X16 @ X17)
% 0.20/0.55          | ((X17) != (k1_tarski @ X15)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.55  thf('11', plain, (![X15 : $i]: (r2_hidden @ X15 @ (k1_tarski @ X15))),
% 0.20/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.55  thf(t20_mcart_1, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.55       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.55          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('split', [status(esa)], ['12'])).
% 0.20/0.55  thf('14', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('15', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t7_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.55       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X26 : $i, X27 : $i]: ((k1_mcart_1 @ (k4_tarski @ X26 @ X27)) = (X26))),
% 0.20/0.55      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.55  thf('17', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf('18', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['14', '17'])).
% 0.20/0.55  thf('19', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['14', '17'])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X26 : $i, X28 : $i]: ((k2_mcart_1 @ (k4_tarski @ X26 @ X28)) = (X28))),
% 0.20/0.55      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.55  thf('21', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 0.20/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['13', '22'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.55         (((X29) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X31 @ X29)
% 0.20/0.55          | ((sk_B @ X29) != (k4_tarski @ X31 @ X30)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          (((sk_B @ X0) != (sk_A))
% 0.20/0.55           | ~ (r2_hidden @ sk_A @ X0)
% 0.20/0.55           | ((X0) = (k1_xboole_0))))
% 0.20/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.55         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.20/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['11', '25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X29 : $i]:
% 0.20/0.55         (((X29) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X29) @ X29))),
% 0.20/0.55      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X18 @ X17)
% 0.20/0.55          | ((X18) = (X15))
% 0.20/0.55          | ((X17) != (k1_tarski @ X15)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X15 : $i, X18 : $i]:
% 0.20/0.55         (((X18) = (X15)) | ~ (r2_hidden @ X18 @ (k1_tarski @ X15)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.55          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['27', '29'])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('clc', [status(thm)], ['26', '30'])).
% 0.20/0.55  thf(t40_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.20/0.55           = (k4_xboole_0 @ X13 @ X14))),
% 0.20/0.55      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.20/0.55  thf(t65_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.55       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (![X23 : $i, X24 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X23 @ X24)
% 0.20/0.55          | ((k4_xboole_0 @ X24 @ (k1_tarski @ X23)) != (X24)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.20/0.55            != (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.55  thf('35', plain, (![X15 : $i]: (r2_hidden @ X15 @ (k1_tarski @ X15))),
% 0.20/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.55  thf(d3_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.20/0.55       ( ![D:$i]:
% 0.20/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.55           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.55          | (r2_hidden @ X0 @ X2)
% 0.20/0.55          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['35', '37'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.20/0.55           != (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['34', '38'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.20/0.55            != (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A))))
% 0.20/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['31', '39'])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('clc', [status(thm)], ['26', '30'])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((k4_xboole_0 @ X0 @ k1_xboole_0) != (k2_xboole_0 @ X0 @ k1_xboole_0)))
% 0.20/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      ((((k1_xboole_0) != (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))
% 0.20/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '42'])).
% 0.20/0.55  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.55  thf('44', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ X12) = (X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.55  thf('46', plain, (($false) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.55  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('split', [status(esa)], ['12'])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      ((((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_A)))
% 0.20/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.55          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['27', '29'])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.55         (((X29) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X30 @ X29)
% 0.20/0.55          | ((sk_B @ X29) != (k4_tarski @ X31 @ X30)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (((X0) != (k4_tarski @ X2 @ X1))
% 0.20/0.55          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.55          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      (![X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 0.20/0.55          | ((k1_tarski @ (k4_tarski @ X2 @ X1)) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.20/0.55         | ((k1_tarski @ (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_A))
% 0.20/0.55             = (k1_xboole_0))))
% 0.20/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['50', '54'])).
% 0.20/0.55  thf('56', plain, (![X15 : $i]: (r2_hidden @ X15 @ (k1_tarski @ X15))),
% 0.20/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      ((((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_A)))
% 0.20/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.20/0.55           != (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['34', '38'])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.20/0.55            != (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A))))
% 0.20/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((k4_xboole_0 @ X0 @ k1_xboole_0) != (k2_xboole_0 @ X0 @ k1_xboole_0)))
% 0.20/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      ((((k1_xboole_0) != (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))
% 0.20/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['47', '62'])).
% 0.20/0.55  thf('64', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ X12) = (X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.55  thf('66', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['65'])).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['12'])).
% 0.20/0.55  thf('68', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['66', '67'])).
% 0.20/0.55  thf('69', plain, ($false),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['46', '68'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
