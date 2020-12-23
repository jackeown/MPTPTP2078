%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OXXa4aOq7p

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:33 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 360 expanded)
%              Number of leaves         :   26 ( 121 expanded)
%              Depth                    :   30
%              Number of atoms          :  794 (2383 expanded)
%              Number of equality atoms :   56 ( 156 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('8',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','22'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('36',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf('46',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','46'])).

thf('48',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('52',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','55'])).

thf('57',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','45'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('61',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('64',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('65',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('76',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('77',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('88',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['73','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['89'])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['91','92','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OXXa4aOq7p
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:48:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.62/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.62/0.83  % Solved by: fo/fo7.sh
% 0.62/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.83  % done 823 iterations in 0.378s
% 0.62/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.62/0.83  % SZS output start Refutation
% 0.62/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.62/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.62/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.62/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.83  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.62/0.83  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.62/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.62/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.62/0.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.62/0.83  thf(dt_k5_relat_1, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.62/0.83       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.62/0.83  thf('0', plain,
% 0.62/0.83      (![X15 : $i, X16 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X15)
% 0.62/0.83          | ~ (v1_relat_1 @ X16)
% 0.62/0.83          | (v1_relat_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.62/0.83      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.62/0.83  thf(t60_relat_1, axiom,
% 0.62/0.83    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.62/0.83     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.62/0.83  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.62/0.83      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.62/0.83  thf(t45_relat_1, axiom,
% 0.62/0.83    (![A:$i]:
% 0.62/0.83     ( ( v1_relat_1 @ A ) =>
% 0.62/0.83       ( ![B:$i]:
% 0.62/0.83         ( ( v1_relat_1 @ B ) =>
% 0.62/0.83           ( r1_tarski @
% 0.62/0.83             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.62/0.83  thf('2', plain,
% 0.62/0.83      (![X21 : $i, X22 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X21)
% 0.62/0.83          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X22 @ X21)) @ 
% 0.62/0.83             (k2_relat_1 @ X21))
% 0.62/0.83          | ~ (v1_relat_1 @ X22))),
% 0.62/0.83      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.62/0.83  thf('3', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.62/0.83           k1_xboole_0)
% 0.62/0.83          | ~ (v1_relat_1 @ X0)
% 0.62/0.83          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['1', '2'])).
% 0.62/0.83  thf(t62_relat_1, conjecture,
% 0.62/0.83    (![A:$i]:
% 0.62/0.83     ( ( v1_relat_1 @ A ) =>
% 0.62/0.83       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.62/0.83         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.62/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.83    (~( ![A:$i]:
% 0.62/0.83        ( ( v1_relat_1 @ A ) =>
% 0.62/0.83          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.62/0.83            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.62/0.83    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.62/0.83  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf(cc1_relat_1, axiom,
% 0.62/0.83    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.62/0.83  thf('5', plain, (![X14 : $i]: ((v1_relat_1 @ X14) | ~ (v1_xboole_0 @ X14))),
% 0.62/0.83      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.62/0.83  thf('6', plain,
% 0.62/0.83      (![X15 : $i, X16 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X15)
% 0.62/0.83          | ~ (v1_relat_1 @ X16)
% 0.62/0.83          | (v1_relat_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.62/0.83      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.62/0.83  thf('7', plain, (![X14 : $i]: ((v1_relat_1 @ X14) | ~ (v1_xboole_0 @ X14))),
% 0.62/0.83      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.62/0.83  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.62/0.83      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.62/0.83  thf(t44_relat_1, axiom,
% 0.62/0.83    (![A:$i]:
% 0.62/0.83     ( ( v1_relat_1 @ A ) =>
% 0.62/0.83       ( ![B:$i]:
% 0.62/0.83         ( ( v1_relat_1 @ B ) =>
% 0.62/0.83           ( r1_tarski @
% 0.62/0.83             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.62/0.83  thf('9', plain,
% 0.62/0.83      (![X19 : $i, X20 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X19)
% 0.62/0.83          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X20 @ X19)) @ 
% 0.62/0.83             (k1_relat_1 @ X20))
% 0.62/0.83          | ~ (v1_relat_1 @ X20))),
% 0.62/0.83      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.62/0.83  thf('10', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.62/0.83           k1_xboole_0)
% 0.62/0.83          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.62/0.83          | ~ (v1_relat_1 @ X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['8', '9'])).
% 0.62/0.83  thf('11', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.62/0.83          | ~ (v1_relat_1 @ X0)
% 0.62/0.83          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.62/0.83             k1_xboole_0))),
% 0.62/0.83      inference('sup-', [status(thm)], ['7', '10'])).
% 0.62/0.83  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.62/0.83  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.62/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.62/0.83  thf('13', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X0)
% 0.62/0.83          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.62/0.83             k1_xboole_0))),
% 0.62/0.83      inference('demod', [status(thm)], ['11', '12'])).
% 0.62/0.83  thf(l32_xboole_1, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.62/0.83  thf('14', plain,
% 0.62/0.83      (![X8 : $i, X10 : $i]:
% 0.62/0.83         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.62/0.83      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.62/0.83  thf('15', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X0)
% 0.62/0.83          | ((k4_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.62/0.83              k1_xboole_0) = (k1_xboole_0)))),
% 0.62/0.83      inference('sup-', [status(thm)], ['13', '14'])).
% 0.62/0.83  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.62/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.62/0.83  thf(t3_xboole_0, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.62/0.83            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.62/0.83       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.62/0.83            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.62/0.83  thf('17', plain,
% 0.62/0.83      (![X4 : $i, X5 : $i]:
% 0.62/0.83         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 0.62/0.83      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.62/0.83  thf(d1_xboole_0, axiom,
% 0.62/0.83    (![A:$i]:
% 0.62/0.83     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.62/0.83  thf('18', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.83  thf('19', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.62/0.83      inference('sup-', [status(thm)], ['17', '18'])).
% 0.62/0.83  thf('20', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.62/0.83      inference('sup-', [status(thm)], ['16', '19'])).
% 0.62/0.83  thf(t83_xboole_1, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.62/0.83  thf('21', plain,
% 0.62/0.83      (![X11 : $i, X12 : $i]:
% 0.62/0.83         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.62/0.83      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.62/0.83  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.62/0.83      inference('sup-', [status(thm)], ['20', '21'])).
% 0.62/0.83  thf('23', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X0)
% 0.62/0.83          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.62/0.83      inference('demod', [status(thm)], ['15', '22'])).
% 0.62/0.83  thf(fc8_relat_1, axiom,
% 0.62/0.83    (![A:$i]:
% 0.62/0.83     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.62/0.83       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.62/0.83  thf('24', plain,
% 0.62/0.83      (![X17 : $i]:
% 0.62/0.83         (~ (v1_xboole_0 @ (k1_relat_1 @ X17))
% 0.62/0.83          | ~ (v1_relat_1 @ X17)
% 0.62/0.83          | (v1_xboole_0 @ X17))),
% 0.62/0.83      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.62/0.83  thf('25', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.62/0.83          | ~ (v1_relat_1 @ X0)
% 0.62/0.83          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.62/0.83          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.62/0.83      inference('sup-', [status(thm)], ['23', '24'])).
% 0.62/0.83  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.62/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.62/0.83  thf('27', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X0)
% 0.62/0.83          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.62/0.83          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.62/0.83      inference('demod', [status(thm)], ['25', '26'])).
% 0.62/0.83  thf('28', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X0)
% 0.62/0.83          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.62/0.83          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.62/0.83          | ~ (v1_relat_1 @ X0))),
% 0.62/0.83      inference('sup-', [status(thm)], ['6', '27'])).
% 0.62/0.83  thf('29', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.62/0.83          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.62/0.83          | ~ (v1_relat_1 @ X0))),
% 0.62/0.83      inference('simplify', [status(thm)], ['28'])).
% 0.62/0.83  thf('30', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.62/0.83          | ~ (v1_relat_1 @ X0)
% 0.62/0.83          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.62/0.83      inference('sup-', [status(thm)], ['5', '29'])).
% 0.62/0.83  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.62/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.62/0.83  thf('32', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.62/0.83      inference('demod', [status(thm)], ['30', '31'])).
% 0.62/0.83  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf(l13_xboole_0, axiom,
% 0.62/0.83    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.62/0.83  thf('34', plain,
% 0.62/0.83      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.62/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.62/0.83  thf('35', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.62/0.83      inference('demod', [status(thm)], ['30', '31'])).
% 0.62/0.83  thf('36', plain,
% 0.62/0.83      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.62/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.62/0.83  thf('37', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X0)
% 0.62/0.83          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.62/0.83      inference('sup-', [status(thm)], ['35', '36'])).
% 0.62/0.83  thf('38', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.62/0.83          | ~ (v1_xboole_0 @ X0)
% 0.62/0.83          | ~ (v1_relat_1 @ X1))),
% 0.62/0.83      inference('sup+', [status(thm)], ['34', '37'])).
% 0.62/0.83  thf('39', plain,
% 0.62/0.83      (![X15 : $i, X16 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X15)
% 0.62/0.83          | ~ (v1_relat_1 @ X16)
% 0.62/0.83          | (v1_relat_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.62/0.83      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.62/0.83  thf('40', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((v1_relat_1 @ k1_xboole_0)
% 0.62/0.83          | ~ (v1_relat_1 @ X0)
% 0.62/0.83          | ~ (v1_xboole_0 @ X1)
% 0.62/0.83          | ~ (v1_relat_1 @ X0)
% 0.62/0.83          | ~ (v1_relat_1 @ X1))),
% 0.62/0.83      inference('sup+', [status(thm)], ['38', '39'])).
% 0.62/0.83  thf('41', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X1)
% 0.62/0.83          | ~ (v1_xboole_0 @ X1)
% 0.62/0.83          | ~ (v1_relat_1 @ X0)
% 0.62/0.83          | (v1_relat_1 @ k1_xboole_0))),
% 0.62/0.83      inference('simplify', [status(thm)], ['40'])).
% 0.62/0.83  thf('42', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         ((v1_relat_1 @ k1_xboole_0)
% 0.62/0.83          | ~ (v1_xboole_0 @ X0)
% 0.62/0.83          | ~ (v1_relat_1 @ X0))),
% 0.62/0.83      inference('sup-', [status(thm)], ['33', '41'])).
% 0.62/0.83  thf('43', plain, (![X14 : $i]: ((v1_relat_1 @ X14) | ~ (v1_xboole_0 @ X14))),
% 0.62/0.83      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.62/0.83  thf('44', plain,
% 0.62/0.83      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.62/0.83      inference('clc', [status(thm)], ['42', '43'])).
% 0.62/0.83  thf('45', plain,
% 0.62/0.83      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.62/0.83      inference('sup-', [status(thm)], ['32', '44'])).
% 0.62/0.83  thf('46', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.62/0.83      inference('sup-', [status(thm)], ['4', '45'])).
% 0.62/0.83  thf('47', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.62/0.83           k1_xboole_0)
% 0.62/0.83          | ~ (v1_relat_1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['3', '46'])).
% 0.62/0.83  thf('48', plain,
% 0.62/0.83      (![X8 : $i, X10 : $i]:
% 0.62/0.83         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.62/0.83      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.62/0.83  thf('49', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X0)
% 0.62/0.83          | ((k4_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.62/0.83              k1_xboole_0) = (k1_xboole_0)))),
% 0.62/0.83      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.83  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.62/0.83      inference('sup-', [status(thm)], ['20', '21'])).
% 0.62/0.83  thf('51', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X0)
% 0.62/0.83          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.62/0.83      inference('demod', [status(thm)], ['49', '50'])).
% 0.62/0.83  thf(fc9_relat_1, axiom,
% 0.62/0.83    (![A:$i]:
% 0.62/0.83     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.62/0.83       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.62/0.83  thf('52', plain,
% 0.62/0.83      (![X18 : $i]:
% 0.62/0.83         (~ (v1_xboole_0 @ (k2_relat_1 @ X18))
% 0.62/0.83          | ~ (v1_relat_1 @ X18)
% 0.62/0.83          | (v1_xboole_0 @ X18))),
% 0.62/0.83      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.62/0.83  thf('53', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.62/0.83          | ~ (v1_relat_1 @ X0)
% 0.62/0.83          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.62/0.83          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.62/0.83      inference('sup-', [status(thm)], ['51', '52'])).
% 0.62/0.83  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.62/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.62/0.83  thf('55', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X0)
% 0.62/0.83          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.62/0.83          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.62/0.83      inference('demod', [status(thm)], ['53', '54'])).
% 0.62/0.83  thf('56', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ k1_xboole_0)
% 0.62/0.83          | ~ (v1_relat_1 @ X0)
% 0.62/0.83          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.62/0.83          | ~ (v1_relat_1 @ X0))),
% 0.62/0.83      inference('sup-', [status(thm)], ['0', '55'])).
% 0.62/0.83  thf('57', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.62/0.83      inference('sup-', [status(thm)], ['4', '45'])).
% 0.62/0.83  thf('58', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X0)
% 0.62/0.83          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.62/0.83          | ~ (v1_relat_1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['56', '57'])).
% 0.62/0.83  thf('59', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.62/0.83      inference('simplify', [status(thm)], ['58'])).
% 0.62/0.83  thf('60', plain,
% 0.62/0.83      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.62/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.62/0.83  thf('61', plain,
% 0.62/0.83      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.62/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.62/0.83  thf('62', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.83      inference('sup+', [status(thm)], ['60', '61'])).
% 0.62/0.83  thf('63', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.83      inference('sup+', [status(thm)], ['60', '61'])).
% 0.62/0.83  thf('64', plain,
% 0.62/0.83      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.62/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.62/0.83  thf('65', plain,
% 0.62/0.83      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.62/0.83        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf('66', plain,
% 0.62/0.83      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.62/0.83         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.62/0.83      inference('split', [status(esa)], ['65'])).
% 0.62/0.83  thf('67', plain,
% 0.62/0.83      ((![X0 : $i]:
% 0.62/0.83          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.62/0.83         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.62/0.83      inference('sup-', [status(thm)], ['64', '66'])).
% 0.62/0.83  thf('68', plain,
% 0.62/0.83      ((![X0 : $i, X1 : $i]:
% 0.62/0.83          (((X0) != (k1_xboole_0))
% 0.62/0.83           | ~ (v1_xboole_0 @ X0)
% 0.62/0.83           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.62/0.83           | ~ (v1_xboole_0 @ X1)))
% 0.62/0.83         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.62/0.83      inference('sup-', [status(thm)], ['63', '67'])).
% 0.62/0.83  thf('69', plain,
% 0.62/0.83      ((![X1 : $i]:
% 0.62/0.83          (~ (v1_xboole_0 @ X1)
% 0.62/0.83           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.62/0.83           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.62/0.83         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.62/0.83      inference('simplify', [status(thm)], ['68'])).
% 0.62/0.83  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.62/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.62/0.83  thf('71', plain,
% 0.62/0.83      ((![X1 : $i]:
% 0.62/0.83          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))))
% 0.62/0.83         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.62/0.83      inference('simplify_reflect+', [status(thm)], ['69', '70'])).
% 0.62/0.83  thf('72', plain,
% 0.62/0.83      ((![X0 : $i, X1 : $i]:
% 0.62/0.83          (~ (v1_xboole_0 @ X0)
% 0.62/0.83           | ~ (v1_xboole_0 @ X0)
% 0.62/0.83           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.62/0.83           | ~ (v1_xboole_0 @ X1)))
% 0.62/0.83         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.62/0.83      inference('sup-', [status(thm)], ['62', '71'])).
% 0.62/0.83  thf('73', plain,
% 0.62/0.83      ((![X0 : $i, X1 : $i]:
% 0.62/0.83          (~ (v1_xboole_0 @ X1)
% 0.62/0.83           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.62/0.83           | ~ (v1_xboole_0 @ X0)))
% 0.62/0.83         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.62/0.83      inference('simplify', [status(thm)], ['72'])).
% 0.62/0.83  thf('74', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.62/0.83      inference('demod', [status(thm)], ['30', '31'])).
% 0.62/0.83  thf('75', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.83      inference('sup+', [status(thm)], ['60', '61'])).
% 0.62/0.83  thf('76', plain,
% 0.62/0.83      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.62/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.62/0.83  thf('77', plain,
% 0.62/0.83      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.62/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.83      inference('split', [status(esa)], ['65'])).
% 0.62/0.83  thf('78', plain,
% 0.62/0.83      ((![X0 : $i]:
% 0.62/0.83          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.62/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.83      inference('sup-', [status(thm)], ['76', '77'])).
% 0.62/0.83  thf('79', plain,
% 0.62/0.83      ((![X0 : $i, X1 : $i]:
% 0.62/0.83          (((X0) != (k1_xboole_0))
% 0.62/0.83           | ~ (v1_xboole_0 @ X0)
% 0.62/0.83           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.62/0.83           | ~ (v1_xboole_0 @ X1)))
% 0.62/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.83      inference('sup-', [status(thm)], ['75', '78'])).
% 0.62/0.83  thf('80', plain,
% 0.62/0.83      ((![X1 : $i]:
% 0.62/0.83          (~ (v1_xboole_0 @ X1)
% 0.62/0.83           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.62/0.83           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.62/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.83      inference('simplify', [status(thm)], ['79'])).
% 0.62/0.83  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.62/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.62/0.83  thf('82', plain,
% 0.62/0.83      ((![X1 : $i]:
% 0.62/0.83          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.62/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.83      inference('simplify_reflect+', [status(thm)], ['80', '81'])).
% 0.62/0.83  thf('83', plain,
% 0.62/0.83      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.62/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.62/0.83      inference('sup-', [status(thm)], ['74', '82'])).
% 0.62/0.83  thf('84', plain, ((v1_relat_1 @ sk_A)),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.62/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.62/0.83  thf('86', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.62/0.83      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.62/0.83  thf('87', plain,
% 0.62/0.83      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.62/0.83       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.62/0.83      inference('split', [status(esa)], ['65'])).
% 0.62/0.83  thf('88', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.62/0.83      inference('sat_resolution*', [status(thm)], ['86', '87'])).
% 0.62/0.83  thf('89', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         (~ (v1_xboole_0 @ X1)
% 0.62/0.83          | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.62/0.83          | ~ (v1_xboole_0 @ X0))),
% 0.62/0.83      inference('simpl_trail', [status(thm)], ['73', '88'])).
% 0.62/0.83  thf('90', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)))),
% 0.62/0.83      inference('condensation', [status(thm)], ['89'])).
% 0.62/0.83  thf('91', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.62/0.83      inference('sup-', [status(thm)], ['59', '90'])).
% 0.62/0.83  thf('92', plain, ((v1_relat_1 @ sk_A)),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.62/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.62/0.83  thf('94', plain, ($false),
% 0.62/0.83      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.62/0.83  
% 0.62/0.83  % SZS output end Refutation
% 0.62/0.83  
% 0.62/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
