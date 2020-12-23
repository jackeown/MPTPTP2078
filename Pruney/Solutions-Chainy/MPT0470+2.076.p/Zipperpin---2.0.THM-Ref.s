%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5a022R3Hpu

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:37 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 305 expanded)
%              Number of leaves         :   21 ( 100 expanded)
%              Depth                    :   31
%              Number of atoms          :  745 (2045 expanded)
%              Number of equality atoms :   55 ( 150 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','41'])).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','50'])).

thf('52',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','40'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('60',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','62'])).

thf('64',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('72',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('83',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['68','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['84'])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['86','87','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5a022R3Hpu
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:37:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.81  % Solved by: fo/fo7.sh
% 0.60/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.81  % done 724 iterations in 0.349s
% 0.60/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.81  % SZS output start Refutation
% 0.60/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.81  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.60/0.81  thf(dt_k5_relat_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.60/0.81       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.60/0.81  thf('0', plain,
% 0.60/0.81      (![X6 : $i, X7 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X6)
% 0.60/0.81          | ~ (v1_relat_1 @ X7)
% 0.60/0.81          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 0.60/0.81      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.60/0.81  thf(t60_relat_1, axiom,
% 0.60/0.81    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.60/0.81     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.60/0.81  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.81      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.60/0.81  thf(t45_relat_1, axiom,
% 0.60/0.81    (![A:$i]:
% 0.60/0.81     ( ( v1_relat_1 @ A ) =>
% 0.60/0.81       ( ![B:$i]:
% 0.60/0.81         ( ( v1_relat_1 @ B ) =>
% 0.60/0.81           ( r1_tarski @
% 0.60/0.81             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.60/0.81  thf('2', plain,
% 0.60/0.81      (![X12 : $i, X13 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X12)
% 0.60/0.81          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X13 @ X12)) @ 
% 0.60/0.81             (k2_relat_1 @ X12))
% 0.60/0.81          | ~ (v1_relat_1 @ X13))),
% 0.60/0.81      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.60/0.81  thf('3', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.60/0.81           k1_xboole_0)
% 0.60/0.81          | ~ (v1_relat_1 @ X0)
% 0.60/0.81          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.60/0.81      inference('sup+', [status(thm)], ['1', '2'])).
% 0.60/0.81  thf(t62_relat_1, conjecture,
% 0.60/0.81    (![A:$i]:
% 0.60/0.81     ( ( v1_relat_1 @ A ) =>
% 0.60/0.81       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.60/0.81         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.60/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.81    (~( ![A:$i]:
% 0.60/0.81        ( ( v1_relat_1 @ A ) =>
% 0.60/0.81          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.60/0.81            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.60/0.81    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.60/0.81  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf(cc1_relat_1, axiom,
% 0.60/0.81    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.60/0.81  thf('5', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.60/0.81      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.60/0.81  thf('6', plain,
% 0.60/0.81      (![X6 : $i, X7 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X6)
% 0.60/0.81          | ~ (v1_relat_1 @ X7)
% 0.60/0.81          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 0.60/0.81      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.60/0.81  thf('7', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.60/0.81      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.60/0.81  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.81      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.60/0.81  thf(t44_relat_1, axiom,
% 0.60/0.81    (![A:$i]:
% 0.60/0.81     ( ( v1_relat_1 @ A ) =>
% 0.60/0.81       ( ![B:$i]:
% 0.60/0.81         ( ( v1_relat_1 @ B ) =>
% 0.60/0.81           ( r1_tarski @
% 0.60/0.81             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.60/0.81  thf('9', plain,
% 0.60/0.81      (![X10 : $i, X11 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X10)
% 0.60/0.81          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 0.60/0.81             (k1_relat_1 @ X11))
% 0.60/0.81          | ~ (v1_relat_1 @ X11))),
% 0.60/0.81      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.60/0.81  thf('10', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.60/0.81           k1_xboole_0)
% 0.60/0.81          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.60/0.81          | ~ (v1_relat_1 @ X0))),
% 0.60/0.81      inference('sup+', [status(thm)], ['8', '9'])).
% 0.60/0.81  thf('11', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.60/0.81          | ~ (v1_relat_1 @ X0)
% 0.60/0.81          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.60/0.81             k1_xboole_0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['7', '10'])).
% 0.60/0.81  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.60/0.81  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.81  thf('13', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X0)
% 0.60/0.81          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.60/0.81             k1_xboole_0))),
% 0.60/0.81      inference('demod', [status(thm)], ['11', '12'])).
% 0.60/0.81  thf(l32_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.60/0.81  thf('14', plain,
% 0.60/0.81      (![X1 : $i, X3 : $i]:
% 0.60/0.81         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 0.60/0.81      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.60/0.81  thf('15', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X0)
% 0.60/0.81          | ((k4_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.60/0.81              k1_xboole_0) = (k1_xboole_0)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['13', '14'])).
% 0.60/0.81  thf(t3_boole, axiom,
% 0.60/0.81    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.60/0.81  thf('16', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.60/0.81      inference('cnf', [status(esa)], [t3_boole])).
% 0.60/0.81  thf('17', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X0)
% 0.60/0.81          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.60/0.81      inference('demod', [status(thm)], ['15', '16'])).
% 0.60/0.81  thf(fc8_relat_1, axiom,
% 0.60/0.81    (![A:$i]:
% 0.60/0.81     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.60/0.81       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.60/0.81  thf('18', plain,
% 0.60/0.81      (![X8 : $i]:
% 0.60/0.81         (~ (v1_xboole_0 @ (k1_relat_1 @ X8))
% 0.60/0.81          | ~ (v1_relat_1 @ X8)
% 0.60/0.81          | (v1_xboole_0 @ X8))),
% 0.60/0.81      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.60/0.81  thf('19', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.60/0.81          | ~ (v1_relat_1 @ X0)
% 0.60/0.81          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.60/0.81          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['17', '18'])).
% 0.60/0.81  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.81  thf('21', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X0)
% 0.60/0.81          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.60/0.81          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.60/0.81      inference('demod', [status(thm)], ['19', '20'])).
% 0.60/0.81  thf('22', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X0)
% 0.60/0.81          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.60/0.81          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.60/0.81          | ~ (v1_relat_1 @ X0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['6', '21'])).
% 0.60/0.81  thf('23', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.60/0.81          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.60/0.81          | ~ (v1_relat_1 @ X0))),
% 0.60/0.81      inference('simplify', [status(thm)], ['22'])).
% 0.60/0.81  thf('24', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.60/0.81          | ~ (v1_relat_1 @ X0)
% 0.60/0.81          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['5', '23'])).
% 0.60/0.81  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.81  thf('26', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.60/0.81      inference('demod', [status(thm)], ['24', '25'])).
% 0.60/0.81  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('28', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.60/0.81      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.60/0.81  thf(l13_xboole_0, axiom,
% 0.60/0.81    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.60/0.81  thf('29', plain,
% 0.60/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.81  thf('30', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.60/0.81      inference('demod', [status(thm)], ['24', '25'])).
% 0.60/0.81  thf('31', plain,
% 0.60/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.81  thf('32', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X0)
% 0.60/0.81          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['30', '31'])).
% 0.60/0.81  thf('33', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.60/0.81          | ~ (v1_xboole_0 @ X0)
% 0.60/0.81          | ~ (v1_relat_1 @ X1))),
% 0.60/0.81      inference('sup+', [status(thm)], ['29', '32'])).
% 0.60/0.81  thf('34', plain,
% 0.60/0.81      (![X6 : $i, X7 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X6)
% 0.60/0.81          | ~ (v1_relat_1 @ X7)
% 0.60/0.81          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 0.60/0.81      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.60/0.81  thf('35', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         ((v1_relat_1 @ k1_xboole_0)
% 0.60/0.81          | ~ (v1_relat_1 @ X0)
% 0.60/0.81          | ~ (v1_xboole_0 @ X1)
% 0.60/0.81          | ~ (v1_relat_1 @ X0)
% 0.60/0.81          | ~ (v1_relat_1 @ X1))),
% 0.60/0.81      inference('sup+', [status(thm)], ['33', '34'])).
% 0.60/0.81  thf('36', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X1)
% 0.60/0.81          | ~ (v1_xboole_0 @ X1)
% 0.60/0.81          | ~ (v1_relat_1 @ X0)
% 0.60/0.81          | (v1_relat_1 @ k1_xboole_0))),
% 0.60/0.81      inference('simplify', [status(thm)], ['35'])).
% 0.60/0.81  thf('37', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (~ (v1_xboole_0 @ X0)
% 0.60/0.81          | (v1_relat_1 @ k1_xboole_0)
% 0.60/0.81          | ~ (v1_relat_1 @ X1)
% 0.60/0.81          | ~ (v1_xboole_0 @ X0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['28', '36'])).
% 0.60/0.81  thf('38', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X1)
% 0.60/0.81          | (v1_relat_1 @ k1_xboole_0)
% 0.60/0.81          | ~ (v1_xboole_0 @ X0))),
% 0.60/0.81      inference('simplify', [status(thm)], ['37'])).
% 0.60/0.81  thf('39', plain,
% 0.60/0.81      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['27', '38'])).
% 0.60/0.81  thf('40', plain,
% 0.60/0.81      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['26', '39'])).
% 0.60/0.81  thf('41', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.60/0.81      inference('sup-', [status(thm)], ['4', '40'])).
% 0.60/0.81  thf('42', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.60/0.81           k1_xboole_0)
% 0.60/0.81          | ~ (v1_relat_1 @ X0))),
% 0.60/0.81      inference('demod', [status(thm)], ['3', '41'])).
% 0.60/0.81  thf('43', plain,
% 0.60/0.81      (![X1 : $i, X3 : $i]:
% 0.60/0.81         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 0.60/0.81      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.60/0.81  thf('44', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X0)
% 0.60/0.81          | ((k4_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.60/0.81              k1_xboole_0) = (k1_xboole_0)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['42', '43'])).
% 0.60/0.81  thf('45', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.60/0.81      inference('cnf', [status(esa)], [t3_boole])).
% 0.60/0.81  thf('46', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X0)
% 0.60/0.81          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.60/0.81      inference('demod', [status(thm)], ['44', '45'])).
% 0.60/0.81  thf(fc9_relat_1, axiom,
% 0.60/0.81    (![A:$i]:
% 0.60/0.81     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.60/0.81       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.60/0.81  thf('47', plain,
% 0.60/0.81      (![X9 : $i]:
% 0.60/0.81         (~ (v1_xboole_0 @ (k2_relat_1 @ X9))
% 0.60/0.81          | ~ (v1_relat_1 @ X9)
% 0.60/0.81          | (v1_xboole_0 @ X9))),
% 0.60/0.81      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.60/0.81  thf('48', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.60/0.81          | ~ (v1_relat_1 @ X0)
% 0.60/0.81          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.60/0.81          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['46', '47'])).
% 0.60/0.81  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.81  thf('50', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X0)
% 0.60/0.81          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.60/0.81          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.60/0.81      inference('demod', [status(thm)], ['48', '49'])).
% 0.60/0.81  thf('51', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ k1_xboole_0)
% 0.60/0.81          | ~ (v1_relat_1 @ X0)
% 0.60/0.81          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.60/0.81          | ~ (v1_relat_1 @ X0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['0', '50'])).
% 0.60/0.81  thf('52', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.60/0.81      inference('sup-', [status(thm)], ['4', '40'])).
% 0.60/0.81  thf('53', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X0)
% 0.60/0.81          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.60/0.81          | ~ (v1_relat_1 @ X0))),
% 0.60/0.81      inference('demod', [status(thm)], ['51', '52'])).
% 0.60/0.81  thf('54', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.60/0.81      inference('simplify', [status(thm)], ['53'])).
% 0.60/0.81  thf('55', plain,
% 0.60/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.81  thf('56', plain,
% 0.60/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.81  thf('57', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.60/0.81      inference('sup+', [status(thm)], ['55', '56'])).
% 0.60/0.81  thf('58', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.60/0.81      inference('sup+', [status(thm)], ['55', '56'])).
% 0.60/0.81  thf('59', plain,
% 0.60/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.81  thf('60', plain,
% 0.60/0.81      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.60/0.81        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('61', plain,
% 0.60/0.81      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.60/0.81         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.60/0.81      inference('split', [status(esa)], ['60'])).
% 0.60/0.81  thf('62', plain,
% 0.60/0.81      ((![X0 : $i]:
% 0.60/0.81          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.60/0.81         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.60/0.81      inference('sup-', [status(thm)], ['59', '61'])).
% 0.60/0.81  thf('63', plain,
% 0.60/0.81      ((![X0 : $i, X1 : $i]:
% 0.60/0.81          (((X0) != (k1_xboole_0))
% 0.60/0.81           | ~ (v1_xboole_0 @ X0)
% 0.60/0.81           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.60/0.81           | ~ (v1_xboole_0 @ X1)))
% 0.60/0.81         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.60/0.81      inference('sup-', [status(thm)], ['58', '62'])).
% 0.60/0.81  thf('64', plain,
% 0.60/0.81      ((![X1 : $i]:
% 0.60/0.81          (~ (v1_xboole_0 @ X1)
% 0.60/0.81           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.60/0.81           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.60/0.81         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.60/0.81      inference('simplify', [status(thm)], ['63'])).
% 0.60/0.81  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.81  thf('66', plain,
% 0.60/0.81      ((![X1 : $i]:
% 0.60/0.81          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))))
% 0.60/0.81         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.60/0.81      inference('simplify_reflect+', [status(thm)], ['64', '65'])).
% 0.60/0.81  thf('67', plain,
% 0.60/0.81      ((![X0 : $i, X1 : $i]:
% 0.60/0.81          (~ (v1_xboole_0 @ X0)
% 0.60/0.81           | ~ (v1_xboole_0 @ X0)
% 0.60/0.81           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.60/0.81           | ~ (v1_xboole_0 @ X1)))
% 0.60/0.81         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.60/0.81      inference('sup-', [status(thm)], ['57', '66'])).
% 0.60/0.81  thf('68', plain,
% 0.60/0.81      ((![X0 : $i, X1 : $i]:
% 0.60/0.81          (~ (v1_xboole_0 @ X1)
% 0.60/0.81           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.60/0.81           | ~ (v1_xboole_0 @ X0)))
% 0.60/0.81         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.60/0.81      inference('simplify', [status(thm)], ['67'])).
% 0.60/0.81  thf('69', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.60/0.81      inference('demod', [status(thm)], ['24', '25'])).
% 0.60/0.81  thf('70', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.60/0.81      inference('sup+', [status(thm)], ['55', '56'])).
% 0.60/0.81  thf('71', plain,
% 0.60/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.81  thf('72', plain,
% 0.60/0.81      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.60/0.81         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.60/0.81      inference('split', [status(esa)], ['60'])).
% 0.60/0.81  thf('73', plain,
% 0.60/0.81      ((![X0 : $i]:
% 0.60/0.81          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.60/0.81         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.60/0.81      inference('sup-', [status(thm)], ['71', '72'])).
% 0.60/0.81  thf('74', plain,
% 0.60/0.81      ((![X0 : $i, X1 : $i]:
% 0.60/0.81          (((X0) != (k1_xboole_0))
% 0.60/0.81           | ~ (v1_xboole_0 @ X0)
% 0.60/0.81           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.60/0.81           | ~ (v1_xboole_0 @ X1)))
% 0.60/0.81         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.60/0.81      inference('sup-', [status(thm)], ['70', '73'])).
% 0.60/0.81  thf('75', plain,
% 0.60/0.81      ((![X1 : $i]:
% 0.60/0.81          (~ (v1_xboole_0 @ X1)
% 0.60/0.81           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.60/0.81           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.60/0.81         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.60/0.81      inference('simplify', [status(thm)], ['74'])).
% 0.60/0.81  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.81  thf('77', plain,
% 0.60/0.81      ((![X1 : $i]:
% 0.60/0.81          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.60/0.81         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.60/0.81      inference('simplify_reflect+', [status(thm)], ['75', '76'])).
% 0.60/0.81  thf('78', plain,
% 0.60/0.81      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.60/0.81         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.60/0.81      inference('sup-', [status(thm)], ['69', '77'])).
% 0.60/0.81  thf('79', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.81  thf('81', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.60/0.81      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.60/0.81  thf('82', plain,
% 0.60/0.81      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.60/0.81       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.60/0.81      inference('split', [status(esa)], ['60'])).
% 0.60/0.81  thf('83', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.60/0.81      inference('sat_resolution*', [status(thm)], ['81', '82'])).
% 0.60/0.81  thf('84', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (~ (v1_xboole_0 @ X1)
% 0.60/0.81          | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.60/0.81          | ~ (v1_xboole_0 @ X0))),
% 0.60/0.81      inference('simpl_trail', [status(thm)], ['68', '83'])).
% 0.60/0.81  thf('85', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)))),
% 0.60/0.81      inference('condensation', [status(thm)], ['84'])).
% 0.60/0.81  thf('86', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['54', '85'])).
% 0.60/0.81  thf('87', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.81  thf('89', plain, ($false),
% 0.60/0.81      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.60/0.81  
% 0.60/0.81  % SZS output end Refutation
% 0.60/0.81  
% 0.60/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
