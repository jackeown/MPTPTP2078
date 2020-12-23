%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cnSl6aIhMd

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:33 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 273 expanded)
%              Number of leaves         :   24 (  79 expanded)
%              Depth                    :   22
%              Number of atoms          :  786 (3117 expanded)
%              Number of equality atoms :  124 ( 650 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X53: $i,X55: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X53 ) @ X55 )
      | ~ ( r2_hidden @ X53 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('4',plain,(
    ! [X59: $i,X60: $i] :
      ( ( r1_tarski @ X59 @ ( k1_tarski @ X60 ) )
      | ( X59 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('5',plain,(
    ! [X60: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X60 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('8',plain,(
    ! [X63: $i,X64: $i] :
      ( ( X64 != X63 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X64 ) @ ( k1_tarski @ X63 ) )
       != ( k1_tarski @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('9',plain,(
    ! [X63: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X63 ) @ ( k1_tarski @ X63 ) )
     != ( k1_tarski @ X63 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X63: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X63 ) ) ),
    inference(demod,[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('22',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X58: $i,X59: $i] :
      ( ( X59
        = ( k1_tarski @ X58 ) )
      | ( X59 = k1_xboole_0 )
      | ~ ( r1_tarski @ X59 @ ( k1_tarski @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('25',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X56 ) @ X57 )
      | ( r2_hidden @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X53: $i,X55: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X53 ) @ X55 )
      | ~ ( r2_hidden @ X53 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['24','37'])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( r1_xboole_0 @ X19 @ X22 )
      | ~ ( r1_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('46',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X18 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('52',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('53',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['48'])).

thf('54',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['7','14'])).

thf('57',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','60'])).

thf('62',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('65',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('68',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('69',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['64','66','70'])).

thf('72',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['63','71'])).

thf('73',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['61','72'])).

thf('74',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['48'])).

thf('75',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['73','74'])).

thf('76',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['49','75'])).

thf('77',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['47','76'])).

thf('78',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( ( k4_xboole_0 @ X10 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('79',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('82',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_B @ sk_C_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','82'])).

thf('84',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['63','71'])).

thf('85',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','85'])).

thf('87',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['0','86'])).

thf('88',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['63','71'])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cnSl6aIhMd
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.94  % Solved by: fo/fo7.sh
% 0.76/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.94  % done 1472 iterations in 0.483s
% 0.76/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.94  % SZS output start Refutation
% 0.76/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.94  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.76/0.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.94  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.94  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/0.94  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.76/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.94  thf(t43_zfmisc_1, conjecture,
% 0.76/0.94    (![A:$i,B:$i,C:$i]:
% 0.76/0.94     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.76/0.94          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.76/0.94          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.76/0.94          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.76/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.94    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.94        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.76/0.94             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.76/0.94             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.76/0.94             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.76/0.94    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.76/0.94  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(d3_tarski, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( r1_tarski @ A @ B ) <=>
% 0.76/0.94       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.76/0.94  thf('1', plain,
% 0.76/0.94      (![X1 : $i, X3 : $i]:
% 0.76/0.94         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.94  thf(l1_zfmisc_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.76/0.94  thf('2', plain,
% 0.76/0.94      (![X53 : $i, X55 : $i]:
% 0.76/0.94         ((r1_tarski @ (k1_tarski @ X53) @ X55) | ~ (r2_hidden @ X53 @ X55))),
% 0.76/0.94      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.76/0.94  thf('3', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((r1_tarski @ X0 @ X1)
% 0.76/0.94          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.94  thf(l3_zfmisc_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.76/0.94       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.76/0.94  thf('4', plain,
% 0.76/0.94      (![X59 : $i, X60 : $i]:
% 0.76/0.94         ((r1_tarski @ X59 @ (k1_tarski @ X60)) | ((X59) != (k1_xboole_0)))),
% 0.76/0.94      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.76/0.94  thf('5', plain, (![X60 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X60))),
% 0.76/0.94      inference('simplify', [status(thm)], ['4'])).
% 0.76/0.94  thf(d10_xboole_0, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.94  thf('6', plain,
% 0.76/0.94      (![X7 : $i, X9 : $i]:
% 0.76/0.94         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.76/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.94  thf('7', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)
% 0.76/0.94          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['5', '6'])).
% 0.76/0.94  thf(t20_zfmisc_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.76/0.94         ( k1_tarski @ A ) ) <=>
% 0.76/0.94       ( ( A ) != ( B ) ) ))).
% 0.76/0.94  thf('8', plain,
% 0.76/0.94      (![X63 : $i, X64 : $i]:
% 0.76/0.94         (((X64) != (X63))
% 0.76/0.94          | ((k4_xboole_0 @ (k1_tarski @ X64) @ (k1_tarski @ X63))
% 0.76/0.94              != (k1_tarski @ X64)))),
% 0.76/0.94      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.76/0.94  thf('9', plain,
% 0.76/0.94      (![X63 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ (k1_tarski @ X63) @ (k1_tarski @ X63))
% 0.76/0.94           != (k1_tarski @ X63))),
% 0.76/0.94      inference('simplify', [status(thm)], ['8'])).
% 0.76/0.94  thf('10', plain,
% 0.76/0.94      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.76/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.94  thf('11', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.76/0.94      inference('simplify', [status(thm)], ['10'])).
% 0.76/0.94  thf(l32_xboole_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.94  thf('12', plain,
% 0.76/0.94      (![X10 : $i, X12 : $i]:
% 0.76/0.94         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.76/0.94          | ~ (r1_tarski @ X10 @ X12))),
% 0.76/0.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.76/0.94  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['11', '12'])).
% 0.76/0.94  thf('14', plain, (![X63 : $i]: ((k1_xboole_0) != (k1_tarski @ X63))),
% 0.76/0.94      inference('demod', [status(thm)], ['9', '13'])).
% 0.76/0.94  thf('15', plain,
% 0.76/0.94      (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)),
% 0.76/0.94      inference('clc', [status(thm)], ['7', '14'])).
% 0.76/0.94  thf('16', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.76/0.94      inference('sup-', [status(thm)], ['3', '15'])).
% 0.76/0.94  thf(t12_xboole_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.76/0.94  thf('17', plain,
% 0.76/0.94      (![X15 : $i, X16 : $i]:
% 0.76/0.94         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.76/0.94      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.94  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/0.94  thf('19', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('20', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(t7_xboole_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.76/0.94  thf('21', plain,
% 0.76/0.94      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 0.76/0.94      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.76/0.94  thf('22', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.76/0.94      inference('sup+', [status(thm)], ['20', '21'])).
% 0.76/0.94  thf('23', plain,
% 0.76/0.94      (![X58 : $i, X59 : $i]:
% 0.76/0.94         (((X59) = (k1_tarski @ X58))
% 0.76/0.94          | ((X59) = (k1_xboole_0))
% 0.76/0.94          | ~ (r1_tarski @ X59 @ (k1_tarski @ X58)))),
% 0.76/0.94      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.76/0.94  thf('24', plain,
% 0.76/0.94      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.94  thf(l27_zfmisc_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.76/0.94  thf('25', plain,
% 0.76/0.94      (![X56 : $i, X57 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ (k1_tarski @ X56) @ X57) | (r2_hidden @ X56 @ X57))),
% 0.76/0.94      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.76/0.94  thf(symmetry_r1_xboole_0, axiom,
% 0.76/0.94    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.76/0.94  thf('26', plain,
% 0.76/0.94      (![X5 : $i, X6 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.76/0.94      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.76/0.94  thf('27', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.94  thf('28', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.76/0.94      inference('sup+', [status(thm)], ['20', '21'])).
% 0.76/0.94  thf('29', plain,
% 0.76/0.94      (![X15 : $i, X16 : $i]:
% 0.76/0.94         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.76/0.94      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.94  thf('30', plain,
% 0.76/0.94      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.76/0.94      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.94  thf(t70_xboole_1, axiom,
% 0.76/0.94    (![A:$i,B:$i,C:$i]:
% 0.76/0.94     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.76/0.94            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.76/0.94       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.76/0.94            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.76/0.94  thf('31', plain,
% 0.76/0.94      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X19 @ X20)
% 0.76/0.94          | ~ (r1_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X22)))),
% 0.76/0.94      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.76/0.94  thf('32', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A)) | (r1_xboole_0 @ X0 @ sk_B))),
% 0.76/0.94      inference('sup-', [status(thm)], ['30', '31'])).
% 0.76/0.94  thf('33', plain,
% 0.76/0.94      (![X0 : $i]: ((r2_hidden @ sk_A @ X0) | (r1_xboole_0 @ X0 @ sk_B))),
% 0.76/0.94      inference('sup-', [status(thm)], ['27', '32'])).
% 0.76/0.94  thf('34', plain,
% 0.76/0.94      (![X53 : $i, X55 : $i]:
% 0.76/0.94         ((r1_tarski @ (k1_tarski @ X53) @ X55) | ~ (r2_hidden @ X53 @ X55))),
% 0.76/0.94      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.76/0.94  thf('35', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X0 @ sk_B) | (r1_tarski @ (k1_tarski @ sk_A) @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['33', '34'])).
% 0.76/0.94  thf('36', plain,
% 0.76/0.94      (![X10 : $i, X12 : $i]:
% 0.76/0.94         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.76/0.94          | ~ (r1_tarski @ X10 @ X12))),
% 0.76/0.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.76/0.94  thf('37', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X0 @ sk_B)
% 0.76/0.94          | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ X0) = (k1_xboole_0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.94  thf('38', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.76/0.94          | ((sk_B) = (k1_xboole_0))
% 0.76/0.94          | (r1_xboole_0 @ X0 @ sk_B))),
% 0.76/0.94      inference('sup+', [status(thm)], ['24', '37'])).
% 0.76/0.94  thf('39', plain,
% 0.76/0.94      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.94  thf('40', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('41', plain,
% 0.76/0.94      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X19 @ X22)
% 0.76/0.94          | ~ (r1_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X22)))),
% 0.76/0.94      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.76/0.94  thf('42', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 0.76/0.94          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.76/0.94      inference('sup-', [status(thm)], ['40', '41'])).
% 0.76/0.94  thf('43', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (r1_xboole_0 @ X0 @ sk_B)
% 0.76/0.94          | ((sk_B) = (k1_xboole_0))
% 0.76/0.94          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.76/0.94      inference('sup-', [status(thm)], ['39', '42'])).
% 0.76/0.94  thf('44', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((sk_B) = (k1_xboole_0))
% 0.76/0.94          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.76/0.94          | (r1_xboole_0 @ X0 @ sk_C_1)
% 0.76/0.94          | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['38', '43'])).
% 0.76/0.94  thf('45', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X0 @ sk_C_1)
% 0.76/0.94          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.76/0.94          | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.94      inference('simplify', [status(thm)], ['44'])).
% 0.76/0.94  thf(t66_xboole_1, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.76/0.94       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.76/0.94  thf('46', plain,
% 0.76/0.94      (![X18 : $i]: (((X18) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X18 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.76/0.94  thf('47', plain,
% 0.76/0.94      ((((sk_B) = (k1_xboole_0))
% 0.76/0.94        | ((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))
% 0.76/0.94        | ((sk_C_1) = (k1_xboole_0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['45', '46'])).
% 0.76/0.94  thf('48', plain,
% 0.76/0.94      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('49', plain,
% 0.76/0.94      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['48'])).
% 0.76/0.94  thf('50', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('51', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((r1_tarski @ X0 @ X1)
% 0.76/0.94          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.94  thf('52', plain,
% 0.76/0.94      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.94  thf('53', plain,
% 0.76/0.94      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.76/0.94      inference('split', [status(esa)], ['48'])).
% 0.76/0.94  thf('54', plain,
% 0.76/0.94      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.76/0.94         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['52', '53'])).
% 0.76/0.94  thf('55', plain,
% 0.76/0.94      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.76/0.94      inference('simplify', [status(thm)], ['54'])).
% 0.76/0.94  thf('56', plain,
% 0.76/0.94      (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)),
% 0.76/0.94      inference('clc', [status(thm)], ['7', '14'])).
% 0.76/0.94  thf('57', plain,
% 0.76/0.94      ((![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ sk_B))
% 0.76/0.94         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['55', '56'])).
% 0.76/0.94  thf('58', plain,
% 0.76/0.94      ((![X0 : $i]: (r1_tarski @ sk_B @ X0))
% 0.76/0.94         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['51', '57'])).
% 0.76/0.94  thf('59', plain,
% 0.76/0.94      (![X15 : $i, X16 : $i]:
% 0.76/0.94         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.76/0.94      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.94  thf('60', plain,
% 0.76/0.94      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.76/0.94         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['58', '59'])).
% 0.76/0.94  thf('61', plain,
% 0.76/0.94      ((((k1_tarski @ sk_A) = (sk_C_1))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.76/0.94      inference('sup+', [status(thm)], ['50', '60'])).
% 0.76/0.94  thf('62', plain,
% 0.76/0.94      ((((sk_B) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('63', plain,
% 0.76/0.94      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.76/0.94         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.76/0.94      inference('split', [status(esa)], ['62'])).
% 0.76/0.94  thf('64', plain,
% 0.76/0.94      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.76/0.94      inference('split', [status(esa)], ['62'])).
% 0.76/0.94  thf('65', plain,
% 0.76/0.94      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('66', plain,
% 0.76/0.94      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.76/0.94      inference('split', [status(esa)], ['65'])).
% 0.76/0.94  thf('67', plain,
% 0.76/0.94      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.76/0.94      inference('simplify', [status(thm)], ['54'])).
% 0.76/0.94  thf('68', plain,
% 0.76/0.94      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.76/0.94      inference('split', [status(esa)], ['62'])).
% 0.76/0.94  thf('69', plain,
% 0.76/0.94      ((((sk_B) != (sk_B)))
% 0.76/0.94         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['67', '68'])).
% 0.76/0.94  thf('70', plain,
% 0.76/0.94      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.76/0.94      inference('simplify', [status(thm)], ['69'])).
% 0.76/0.94  thf('71', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.76/0.94      inference('sat_resolution*', [status(thm)], ['64', '66', '70'])).
% 0.76/0.94  thf('72', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.76/0.94      inference('simpl_trail', [status(thm)], ['63', '71'])).
% 0.76/0.94  thf('73', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.76/0.94      inference('simplify_reflect-', [status(thm)], ['61', '72'])).
% 0.76/0.94  thf('74', plain,
% 0.76/0.94      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.76/0.94      inference('split', [status(esa)], ['48'])).
% 0.76/0.94  thf('75', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.76/0.94      inference('sat_resolution*', [status(thm)], ['73', '74'])).
% 0.76/0.94  thf('76', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.76/0.94      inference('simpl_trail', [status(thm)], ['49', '75'])).
% 0.76/0.94  thf('77', plain,
% 0.76/0.94      ((((sk_B) = (k1_xboole_0))
% 0.76/0.94        | ((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0)))),
% 0.76/0.94      inference('simplify_reflect-', [status(thm)], ['47', '76'])).
% 0.76/0.94  thf('78', plain,
% 0.76/0.94      (![X10 : $i, X11 : $i]:
% 0.76/0.94         ((r1_tarski @ X10 @ X11)
% 0.76/0.94          | ((k4_xboole_0 @ X10 @ X11) != (k1_xboole_0)))),
% 0.76/0.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.76/0.94  thf('79', plain,
% 0.76/0.94      ((((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.94        | ((sk_B) = (k1_xboole_0))
% 0.76/0.94        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.76/0.94      inference('sup-', [status(thm)], ['77', '78'])).
% 0.76/0.94  thf('80', plain, (((r1_tarski @ sk_B @ sk_C_1) | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.94      inference('simplify', [status(thm)], ['79'])).
% 0.76/0.94  thf('81', plain,
% 0.76/0.94      (![X15 : $i, X16 : $i]:
% 0.76/0.94         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.76/0.94      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.94  thf('82', plain,
% 0.76/0.94      ((((sk_B) = (k1_xboole_0)) | ((k2_xboole_0 @ sk_B @ sk_C_1) = (sk_C_1)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['80', '81'])).
% 0.76/0.94  thf('83', plain,
% 0.76/0.94      ((((k1_tarski @ sk_A) = (sk_C_1)) | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['19', '82'])).
% 0.76/0.94  thf('84', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.76/0.94      inference('simpl_trail', [status(thm)], ['63', '71'])).
% 0.76/0.94  thf('85', plain, (((sk_B) = (k1_xboole_0))),
% 0.76/0.94      inference('simplify_reflect-', [status(thm)], ['83', '84'])).
% 0.76/0.94  thf('86', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 0.76/0.94      inference('demod', [status(thm)], ['18', '85'])).
% 0.76/0.94  thf('87', plain, (((k1_tarski @ sk_A) = (sk_C_1))),
% 0.76/0.94      inference('demod', [status(thm)], ['0', '86'])).
% 0.76/0.94  thf('88', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.76/0.94      inference('simpl_trail', [status(thm)], ['63', '71'])).
% 0.76/0.94  thf('89', plain, ($false),
% 0.76/0.94      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 0.76/0.94  
% 0.76/0.94  % SZS output end Refutation
% 0.76/0.94  
% 0.76/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
