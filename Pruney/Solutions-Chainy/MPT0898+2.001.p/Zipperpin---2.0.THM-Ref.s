%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1vyGbVb9cV

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:42 EST 2020

% Result     : Theorem 3.57s
% Output     : Refutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 473 expanded)
%              Number of leaves         :   16 ( 143 expanded)
%              Depth                    :   28
%              Number of atoms          :  986 (5989 expanded)
%              Number of equality atoms :  138 ( 784 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t58_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
        = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
          = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_mcart_1])).

thf('0',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ X26 )
       != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('2',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X19 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X19 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('9',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X19 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t138_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X12 @ X13 ) @ ( k2_zfmisc_1 @ X14 @ X15 ) )
      | ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ X4 @ X0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X19 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ X26 )
       != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X11 @ X9 ) @ ( k2_zfmisc_1 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_A ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_A ) @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','22'])).

thf('24',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X19 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_A ) @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_A ) @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','25'])).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X19 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X19 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X7 @ X6 ) @ ( k2_zfmisc_1 @ X8 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X4 @ X0 ) )
      | ( r1_tarski @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X4 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ X6 @ X5 @ X4 @ X0 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B ) @ ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B ) @ ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('34',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X12 @ X13 ) @ ( k2_zfmisc_1 @ X14 @ X15 ) )
      | ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X4 @ X3 ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ X3 @ X0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ X5 @ X4 @ X3 ) )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ X5 @ X4 @ X3 ) )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['19'])).

thf('43',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ( X23 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('57',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X24 @ X25 @ X27 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_B @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','57'])).

thf('59',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ X26 )
       != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('65',plain,
    ( ( sk_B = sk_A )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != sk_A ) ),
    inference(demod,[status(thm)],['3','63','64'])).

thf('66',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
 != sk_A ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X24 @ X25 @ X27 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('71',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ X24 @ X25 @ X27 )
      = sk_A ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['67','71'])).

thf('73',plain,(
    $false ),
    inference(simplify,[status(thm)],['72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1vyGbVb9cV
% 0.14/0.37  % Computer   : n001.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 16:06:00 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 3.57/3.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.57/3.75  % Solved by: fo/fo7.sh
% 3.57/3.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.57/3.75  % done 1452 iterations in 3.265s
% 3.57/3.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.57/3.75  % SZS output start Refutation
% 3.57/3.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.57/3.75  thf(sk_B_type, type, sk_B: $i).
% 3.57/3.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.57/3.75  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 3.57/3.75  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 3.57/3.75  thf(sk_A_type, type, sk_A: $i).
% 3.57/3.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.57/3.75  thf(t58_mcart_1, conjecture,
% 3.57/3.75    (![A:$i,B:$i]:
% 3.57/3.75     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 3.57/3.75       ( ( A ) = ( B ) ) ))).
% 3.57/3.75  thf(zf_stmt_0, negated_conjecture,
% 3.57/3.75    (~( ![A:$i,B:$i]:
% 3.57/3.75        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 3.57/3.75          ( ( A ) = ( B ) ) ) )),
% 3.57/3.75    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 3.57/3.75  thf('0', plain,
% 3.57/3.75      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 3.57/3.75         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 3.57/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.57/3.75  thf(t55_mcart_1, axiom,
% 3.57/3.75    (![A:$i,B:$i,C:$i,D:$i]:
% 3.57/3.75     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 3.57/3.75         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 3.57/3.75       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 3.57/3.75  thf('1', plain,
% 3.57/3.75      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.57/3.75         (((k4_zfmisc_1 @ X23 @ X24 @ X25 @ X26) != (k1_xboole_0))
% 3.57/3.75          | ((X26) = (k1_xboole_0))
% 3.57/3.75          | ((X25) = (k1_xboole_0))
% 3.57/3.75          | ((X24) = (k1_xboole_0))
% 3.57/3.75          | ((X23) = (k1_xboole_0)))),
% 3.57/3.75      inference('cnf', [status(esa)], [t55_mcart_1])).
% 3.57/3.75  thf('2', plain,
% 3.57/3.75      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 3.57/3.75        | ((sk_B) = (k1_xboole_0))
% 3.57/3.75        | ((sk_B) = (k1_xboole_0))
% 3.57/3.75        | ((sk_B) = (k1_xboole_0))
% 3.57/3.75        | ((sk_B) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['0', '1'])).
% 3.57/3.75  thf('3', plain,
% 3.57/3.75      ((((sk_B) = (k1_xboole_0))
% 3.57/3.75        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 3.57/3.75      inference('simplify', [status(thm)], ['2'])).
% 3.57/3.75  thf('4', plain,
% 3.57/3.75      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 3.57/3.75         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 3.57/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.57/3.75  thf(d4_zfmisc_1, axiom,
% 3.57/3.75    (![A:$i,B:$i,C:$i,D:$i]:
% 3.57/3.75     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 3.57/3.75       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 3.57/3.75  thf('5', plain,
% 3.57/3.75      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.57/3.75         ((k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22)
% 3.57/3.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X19 @ X20 @ X21) @ X22))),
% 3.57/3.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 3.57/3.75  thf(d10_xboole_0, axiom,
% 3.57/3.75    (![A:$i,B:$i]:
% 3.57/3.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.57/3.75  thf('6', plain,
% 3.57/3.75      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.57/3.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.57/3.75  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.57/3.75      inference('simplify', [status(thm)], ['6'])).
% 3.57/3.75  thf('8', plain,
% 3.57/3.75      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.57/3.75         ((k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22)
% 3.57/3.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X19 @ X20 @ X21) @ X22))),
% 3.57/3.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 3.57/3.75  thf('9', plain,
% 3.57/3.75      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 3.57/3.75         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 3.57/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.57/3.75  thf('10', plain,
% 3.57/3.75      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.57/3.75         ((k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22)
% 3.57/3.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X19 @ X20 @ X21) @ X22))),
% 3.57/3.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 3.57/3.75  thf(t138_zfmisc_1, axiom,
% 3.57/3.75    (![A:$i,B:$i,C:$i,D:$i]:
% 3.57/3.75     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 3.57/3.75       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 3.57/3.75         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 3.57/3.75  thf('11', plain,
% 3.57/3.75      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.57/3.75         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 3.57/3.75          | ~ (r1_tarski @ (k2_zfmisc_1 @ X12 @ X13) @ 
% 3.57/3.75               (k2_zfmisc_1 @ X14 @ X15))
% 3.57/3.75          | (r1_tarski @ X13 @ X15))),
% 3.57/3.75      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 3.57/3.75  thf('12', plain,
% 3.57/3.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.57/3.75         (~ (r1_tarski @ (k2_zfmisc_1 @ X5 @ X4) @ 
% 3.57/3.75             (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 3.57/3.75          | (r1_tarski @ X4 @ X0)
% 3.57/3.75          | ((k2_zfmisc_1 @ X5 @ X4) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['10', '11'])).
% 3.57/3.75  thf('13', plain,
% 3.57/3.75      (![X0 : $i, X1 : $i]:
% 3.57/3.75         (~ (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 3.57/3.75             (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 3.57/3.75          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 3.57/3.75          | (r1_tarski @ X0 @ sk_B))),
% 3.57/3.75      inference('sup-', [status(thm)], ['9', '12'])).
% 3.57/3.75  thf('14', plain,
% 3.57/3.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.57/3.75         (~ (r1_tarski @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ 
% 3.57/3.75             (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 3.57/3.75          | (r1_tarski @ X0 @ sk_B)
% 3.57/3.75          | ((k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['8', '13'])).
% 3.57/3.75  thf('15', plain,
% 3.57/3.75      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.57/3.75         ((k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22)
% 3.57/3.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X19 @ X20 @ X21) @ X22))),
% 3.57/3.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 3.57/3.75  thf('16', plain,
% 3.57/3.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.57/3.75         (~ (r1_tarski @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ 
% 3.57/3.75             (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 3.57/3.75          | (r1_tarski @ X0 @ sk_B)
% 3.57/3.75          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 3.57/3.75      inference('demod', [status(thm)], ['14', '15'])).
% 3.57/3.75  thf('17', plain,
% 3.57/3.75      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 3.57/3.75        | (r1_tarski @ sk_A @ sk_B))),
% 3.57/3.75      inference('sup-', [status(thm)], ['7', '16'])).
% 3.57/3.75  thf('18', plain,
% 3.57/3.75      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.57/3.75         (((k4_zfmisc_1 @ X23 @ X24 @ X25 @ X26) != (k1_xboole_0))
% 3.57/3.75          | ((X26) = (k1_xboole_0))
% 3.57/3.75          | ((X25) = (k1_xboole_0))
% 3.57/3.75          | ((X24) = (k1_xboole_0))
% 3.57/3.75          | ((X23) = (k1_xboole_0)))),
% 3.57/3.75      inference('cnf', [status(esa)], [t55_mcart_1])).
% 3.57/3.75  thf('19', plain,
% 3.57/3.75      ((((k1_xboole_0) != (k1_xboole_0))
% 3.57/3.75        | (r1_tarski @ sk_A @ sk_B)
% 3.57/3.75        | ((sk_A) = (k1_xboole_0))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['17', '18'])).
% 3.57/3.75  thf('20', plain, ((((sk_A) = (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 3.57/3.75      inference('simplify', [status(thm)], ['19'])).
% 3.57/3.75  thf(t118_zfmisc_1, axiom,
% 3.57/3.75    (![A:$i,B:$i,C:$i]:
% 3.57/3.75     ( ( r1_tarski @ A @ B ) =>
% 3.57/3.75       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 3.57/3.75         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 3.57/3.75  thf('21', plain,
% 3.57/3.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.57/3.75         (~ (r1_tarski @ X9 @ X10)
% 3.57/3.75          | (r1_tarski @ (k2_zfmisc_1 @ X11 @ X9) @ (k2_zfmisc_1 @ X11 @ X10)))),
% 3.57/3.75      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 3.57/3.75  thf('22', plain,
% 3.57/3.75      (![X0 : $i]:
% 3.57/3.75         (((sk_A) = (k1_xboole_0))
% 3.57/3.75          | (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_A) @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['20', '21'])).
% 3.57/3.75  thf('23', plain,
% 3.57/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.75         ((r1_tarski @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_A) @ 
% 3.57/3.75           (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ sk_B))
% 3.57/3.75          | ((sk_A) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup+', [status(thm)], ['5', '22'])).
% 3.57/3.75  thf('24', plain,
% 3.57/3.75      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.57/3.75         ((k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22)
% 3.57/3.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X19 @ X20 @ X21) @ X22))),
% 3.57/3.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 3.57/3.75  thf('25', plain,
% 3.57/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.75         ((r1_tarski @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_A) @ 
% 3.57/3.75           (k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_B))
% 3.57/3.75          | ((sk_A) = (k1_xboole_0)))),
% 3.57/3.75      inference('demod', [status(thm)], ['23', '24'])).
% 3.57/3.75  thf('26', plain,
% 3.57/3.75      (((r1_tarski @ (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_A) @ 
% 3.57/3.75         (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup+', [status(thm)], ['4', '25'])).
% 3.57/3.75  thf('27', plain,
% 3.57/3.75      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.57/3.75         ((k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22)
% 3.57/3.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X19 @ X20 @ X21) @ X22))),
% 3.57/3.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 3.57/3.75  thf('28', plain,
% 3.57/3.75      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.57/3.75         ((k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22)
% 3.57/3.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X19 @ X20 @ X21) @ X22))),
% 3.57/3.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 3.57/3.75  thf(t117_zfmisc_1, axiom,
% 3.57/3.75    (![A:$i,B:$i,C:$i]:
% 3.57/3.75     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.57/3.75          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 3.57/3.75            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 3.57/3.75          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 3.57/3.75  thf('29', plain,
% 3.57/3.75      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.57/3.75         (((X6) = (k1_xboole_0))
% 3.57/3.75          | (r1_tarski @ X7 @ X8)
% 3.57/3.75          | ~ (r1_tarski @ (k2_zfmisc_1 @ X7 @ X6) @ (k2_zfmisc_1 @ X8 @ X6)))),
% 3.57/3.75      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 3.57/3.75  thf('30', plain,
% 3.57/3.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.57/3.75         (~ (r1_tarski @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ 
% 3.57/3.75             (k2_zfmisc_1 @ X4 @ X0))
% 3.57/3.75          | (r1_tarski @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X4)
% 3.57/3.75          | ((X0) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['28', '29'])).
% 3.57/3.75  thf('31', plain,
% 3.57/3.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.57/3.75         (~ (r1_tarski @ (k4_zfmisc_1 @ X6 @ X5 @ X4 @ X0) @ 
% 3.57/3.75             (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 3.57/3.75          | ((X0) = (k1_xboole_0))
% 3.57/3.75          | (r1_tarski @ (k3_zfmisc_1 @ X6 @ X5 @ X4) @ 
% 3.57/3.75             (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['27', '30'])).
% 3.57/3.75  thf('32', plain,
% 3.57/3.75      ((((sk_A) = (k1_xboole_0))
% 3.57/3.75        | (r1_tarski @ (k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) @ 
% 3.57/3.75           (k3_zfmisc_1 @ sk_A @ sk_A @ sk_A))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['26', '31'])).
% 3.57/3.75  thf('33', plain,
% 3.57/3.75      (((r1_tarski @ (k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) @ 
% 3.57/3.75         (k3_zfmisc_1 @ sk_A @ sk_A @ sk_A))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0)))),
% 3.57/3.75      inference('simplify', [status(thm)], ['32'])).
% 3.57/3.75  thf(d3_zfmisc_1, axiom,
% 3.57/3.75    (![A:$i,B:$i,C:$i]:
% 3.57/3.75     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 3.57/3.75       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 3.57/3.75  thf('34', plain,
% 3.57/3.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.57/3.75         ((k3_zfmisc_1 @ X16 @ X17 @ X18)
% 3.57/3.75           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18))),
% 3.57/3.75      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 3.57/3.75  thf('35', plain,
% 3.57/3.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.57/3.75         ((k3_zfmisc_1 @ X16 @ X17 @ X18)
% 3.57/3.75           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18))),
% 3.57/3.75      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 3.57/3.75  thf('36', plain,
% 3.57/3.75      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.57/3.75         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 3.57/3.75          | ~ (r1_tarski @ (k2_zfmisc_1 @ X12 @ X13) @ 
% 3.57/3.75               (k2_zfmisc_1 @ X14 @ X15))
% 3.57/3.75          | (r1_tarski @ X13 @ X15))),
% 3.57/3.75      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 3.57/3.75  thf('37', plain,
% 3.57/3.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.57/3.75         (~ (r1_tarski @ (k2_zfmisc_1 @ X4 @ X3) @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 3.57/3.75          | (r1_tarski @ X3 @ X0)
% 3.57/3.75          | ((k2_zfmisc_1 @ X4 @ X3) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['35', '36'])).
% 3.57/3.75  thf('38', plain,
% 3.57/3.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.57/3.75         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ 
% 3.57/3.75             (k3_zfmisc_1 @ X5 @ X4 @ X3))
% 3.57/3.75          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0) = (k1_xboole_0))
% 3.57/3.75          | (r1_tarski @ X0 @ X3))),
% 3.57/3.75      inference('sup-', [status(thm)], ['34', '37'])).
% 3.57/3.75  thf('39', plain,
% 3.57/3.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.57/3.75         ((k3_zfmisc_1 @ X16 @ X17 @ X18)
% 3.57/3.75           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18))),
% 3.57/3.75      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 3.57/3.75  thf('40', plain,
% 3.57/3.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.57/3.75         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ 
% 3.57/3.75             (k3_zfmisc_1 @ X5 @ X4 @ X3))
% 3.57/3.75          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 3.57/3.75          | (r1_tarski @ X0 @ X3))),
% 3.57/3.75      inference('demod', [status(thm)], ['38', '39'])).
% 3.57/3.75  thf('41', plain,
% 3.57/3.75      ((((sk_A) = (k1_xboole_0))
% 3.57/3.75        | (r1_tarski @ sk_B @ sk_A)
% 3.57/3.75        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['33', '40'])).
% 3.57/3.75  thf('42', plain, ((((sk_A) = (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 3.57/3.75      inference('simplify', [status(thm)], ['19'])).
% 3.57/3.75  thf('43', plain,
% 3.57/3.75      (![X0 : $i, X2 : $i]:
% 3.57/3.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.57/3.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.57/3.75  thf('44', plain,
% 3.57/3.75      ((((sk_A) = (k1_xboole_0))
% 3.57/3.75        | ~ (r1_tarski @ sk_B @ sk_A)
% 3.57/3.75        | ((sk_B) = (sk_A)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['42', '43'])).
% 3.57/3.75  thf('45', plain, (((sk_A) != (sk_B))),
% 3.57/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.57/3.75  thf('46', plain, ((((sk_A) = (k1_xboole_0)) | ~ (r1_tarski @ sk_B @ sk_A))),
% 3.57/3.75      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 3.57/3.75  thf('47', plain,
% 3.57/3.75      ((((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (k1_xboole_0))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0)))),
% 3.57/3.75      inference('clc', [status(thm)], ['41', '46'])).
% 3.57/3.75  thf('48', plain,
% 3.57/3.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.57/3.75         ((k3_zfmisc_1 @ X16 @ X17 @ X18)
% 3.57/3.75           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18))),
% 3.57/3.75      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 3.57/3.75  thf(t113_zfmisc_1, axiom,
% 3.57/3.75    (![A:$i,B:$i]:
% 3.57/3.75     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.57/3.75       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.57/3.75  thf('49', plain,
% 3.57/3.75      (![X3 : $i, X4 : $i]:
% 3.57/3.75         (((X3) = (k1_xboole_0))
% 3.57/3.75          | ((X4) = (k1_xboole_0))
% 3.57/3.75          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 3.57/3.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.57/3.75  thf('50', plain,
% 3.57/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.75         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 3.57/3.75          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 3.57/3.75          | ((X0) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['48', '49'])).
% 3.57/3.75  thf('51', plain,
% 3.57/3.75      ((((k1_xboole_0) != (k1_xboole_0))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0))
% 3.57/3.75        | ((sk_B) = (k1_xboole_0))
% 3.57/3.75        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['47', '50'])).
% 3.57/3.75  thf('52', plain,
% 3.57/3.75      ((((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0))
% 3.57/3.75        | ((sk_B) = (k1_xboole_0))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0)))),
% 3.57/3.75      inference('simplify', [status(thm)], ['51'])).
% 3.57/3.75  thf('53', plain,
% 3.57/3.75      (![X3 : $i, X4 : $i]:
% 3.57/3.75         (((X3) = (k1_xboole_0))
% 3.57/3.75          | ((X4) = (k1_xboole_0))
% 3.57/3.75          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 3.57/3.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.57/3.75  thf('54', plain,
% 3.57/3.75      ((((k1_xboole_0) != (k1_xboole_0))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0))
% 3.57/3.75        | ((sk_B) = (k1_xboole_0))
% 3.57/3.75        | ((sk_B) = (k1_xboole_0))
% 3.57/3.75        | ((sk_B) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['52', '53'])).
% 3.57/3.75  thf('55', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 3.57/3.75      inference('simplify', [status(thm)], ['54'])).
% 3.57/3.75  thf('56', plain,
% 3.57/3.75      (![X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 3.57/3.75         (((X23) != (k1_xboole_0))
% 3.57/3.75          | ((k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27) = (k1_xboole_0)))),
% 3.57/3.75      inference('cnf', [status(esa)], [t55_mcart_1])).
% 3.57/3.75  thf('57', plain,
% 3.57/3.75      (![X24 : $i, X25 : $i, X27 : $i]:
% 3.57/3.75         ((k4_zfmisc_1 @ k1_xboole_0 @ X24 @ X25 @ X27) = (k1_xboole_0))),
% 3.57/3.75      inference('simplify', [status(thm)], ['56'])).
% 3.57/3.75  thf('58', plain,
% 3.57/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.57/3.75         (((k4_zfmisc_1 @ sk_B @ X2 @ X1 @ X0) = (k1_xboole_0))
% 3.57/3.75          | ((sk_A) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup+', [status(thm)], ['55', '57'])).
% 3.57/3.75  thf('59', plain,
% 3.57/3.75      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 3.57/3.75         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 3.57/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.57/3.75  thf('60', plain,
% 3.57/3.75      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup+', [status(thm)], ['58', '59'])).
% 3.57/3.75  thf('61', plain,
% 3.57/3.75      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.57/3.75         (((k4_zfmisc_1 @ X23 @ X24 @ X25 @ X26) != (k1_xboole_0))
% 3.57/3.75          | ((X26) = (k1_xboole_0))
% 3.57/3.75          | ((X25) = (k1_xboole_0))
% 3.57/3.75          | ((X24) = (k1_xboole_0))
% 3.57/3.75          | ((X23) = (k1_xboole_0)))),
% 3.57/3.75      inference('cnf', [status(esa)], [t55_mcart_1])).
% 3.57/3.75  thf('62', plain,
% 3.57/3.75      ((((k1_xboole_0) != (k1_xboole_0))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0))
% 3.57/3.75        | ((sk_A) = (k1_xboole_0)))),
% 3.57/3.75      inference('sup-', [status(thm)], ['60', '61'])).
% 3.57/3.75  thf('63', plain, (((sk_A) = (k1_xboole_0))),
% 3.57/3.75      inference('simplify', [status(thm)], ['62'])).
% 3.57/3.75  thf('64', plain, (((sk_A) = (k1_xboole_0))),
% 3.57/3.75      inference('simplify', [status(thm)], ['62'])).
% 3.57/3.75  thf('65', plain,
% 3.57/3.75      ((((sk_B) = (sk_A))
% 3.57/3.75        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A)))),
% 3.57/3.75      inference('demod', [status(thm)], ['3', '63', '64'])).
% 3.57/3.75  thf('66', plain, (((sk_A) != (sk_B))),
% 3.57/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.57/3.75  thf('67', plain, (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A))),
% 3.57/3.75      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 3.57/3.75  thf('68', plain,
% 3.57/3.75      (![X24 : $i, X25 : $i, X27 : $i]:
% 3.57/3.75         ((k4_zfmisc_1 @ k1_xboole_0 @ X24 @ X25 @ X27) = (k1_xboole_0))),
% 3.57/3.75      inference('simplify', [status(thm)], ['56'])).
% 3.57/3.75  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 3.57/3.75      inference('simplify', [status(thm)], ['62'])).
% 3.57/3.75  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 3.57/3.75      inference('simplify', [status(thm)], ['62'])).
% 3.57/3.75  thf('71', plain,
% 3.57/3.75      (![X24 : $i, X25 : $i, X27 : $i]:
% 3.57/3.75         ((k4_zfmisc_1 @ sk_A @ X24 @ X25 @ X27) = (sk_A))),
% 3.57/3.75      inference('demod', [status(thm)], ['68', '69', '70'])).
% 3.57/3.75  thf('72', plain, (((sk_A) != (sk_A))),
% 3.57/3.75      inference('demod', [status(thm)], ['67', '71'])).
% 3.57/3.75  thf('73', plain, ($false), inference('simplify', [status(thm)], ['72'])).
% 3.57/3.75  
% 3.57/3.75  % SZS output end Refutation
% 3.57/3.75  
% 3.57/3.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
