%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.96Ng36CAGv

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:28 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 945 expanded)
%              Number of leaves         :   22 ( 302 expanded)
%              Depth                    :   28
%              Number of atoms          :  717 (6260 expanded)
%              Number of equality atoms :   62 ( 347 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('25',plain,(
    ! [X10: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X10 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X13 ) @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','29'])).

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

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','45'])).

thf('47',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('50',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('58',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('69',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['52','69'])).

thf('71',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('77',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','44'])).

thf('79',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','44'])).

thf('82',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['80','81'])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['73','82','83','84'])).

thf('86',plain,(
    $false ),
    inference(simplify,[status(thm)],['85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.96Ng36CAGv
% 0.15/0.38  % Computer   : n019.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 15:21:08 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.90/1.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.13  % Solved by: fo/fo7.sh
% 0.90/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.13  % done 1076 iterations in 0.643s
% 0.90/1.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.13  % SZS output start Refutation
% 0.90/1.13  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.13  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.13  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.90/1.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.13  thf(cc1_relat_1, axiom,
% 0.90/1.13    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.90/1.13  thf('0', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.90/1.13      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.90/1.13  thf(dt_k5_relat_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.90/1.13       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.90/1.13  thf('1', plain,
% 0.90/1.13      (![X7 : $i, X8 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X7)
% 0.90/1.13          | ~ (v1_relat_1 @ X8)
% 0.90/1.13          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.90/1.13  thf('2', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.90/1.13      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.90/1.13  thf(t60_relat_1, axiom,
% 0.90/1.13    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.90/1.13     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.90/1.13  thf('3', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.13      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.90/1.13  thf(t44_relat_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( v1_relat_1 @ A ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( v1_relat_1 @ B ) =>
% 0.90/1.13           ( r1_tarski @
% 0.90/1.13             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.90/1.13  thf('4', plain,
% 0.90/1.13      (![X11 : $i, X12 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X11)
% 0.90/1.13          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X12 @ X11)) @ 
% 0.90/1.13             (k1_relat_1 @ X12))
% 0.90/1.13          | ~ (v1_relat_1 @ X12))),
% 0.90/1.13      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.90/1.13  thf('5', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.90/1.13           k1_xboole_0)
% 0.90/1.13          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0))),
% 0.90/1.13      inference('sup+', [status(thm)], ['3', '4'])).
% 0.90/1.13  thf('6', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.90/1.13             k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['2', '5'])).
% 0.90/1.13  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.90/1.13  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.13      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.13  thf('8', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.90/1.13             k1_xboole_0))),
% 0.90/1.13      inference('demod', [status(thm)], ['6', '7'])).
% 0.90/1.13  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.90/1.13  thf('9', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.90/1.13      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.90/1.13  thf(d10_xboole_0, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.13  thf('10', plain,
% 0.90/1.13      (![X1 : $i, X3 : $i]:
% 0.90/1.13         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.90/1.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.13  thf('11', plain,
% 0.90/1.13      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['9', '10'])).
% 0.90/1.13  thf('12', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['8', '11'])).
% 0.90/1.13  thf(fc8_relat_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.90/1.13       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.90/1.13  thf('13', plain,
% 0.90/1.13      (![X9 : $i]:
% 0.90/1.13         (~ (v1_xboole_0 @ (k1_relat_1 @ X9))
% 0.90/1.13          | ~ (v1_relat_1 @ X9)
% 0.90/1.13          | (v1_xboole_0 @ X9))),
% 0.90/1.13      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.90/1.13  thf('14', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.90/1.13          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.13  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.13      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.13  thf('16', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.90/1.13          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.90/1.13      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.13  thf('17', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.90/1.13          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.90/1.13          | ~ (v1_relat_1 @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['1', '16'])).
% 0.90/1.13  thf('18', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.90/1.13          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0))),
% 0.90/1.13      inference('simplify', [status(thm)], ['17'])).
% 0.90/1.13  thf('19', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['0', '18'])).
% 0.90/1.13  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.13      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.13  thf('21', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.90/1.13      inference('demod', [status(thm)], ['19', '20'])).
% 0.90/1.13  thf(l13_xboole_0, axiom,
% 0.90/1.13    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.13  thf('22', plain,
% 0.90/1.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.13  thf('23', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.13  thf(dt_k4_relat_1, axiom,
% 0.90/1.13    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.90/1.13  thf('24', plain,
% 0.90/1.13      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.90/1.13  thf(involutiveness_k4_relat_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.90/1.13  thf('25', plain,
% 0.90/1.13      (![X10 : $i]:
% 0.90/1.13         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 0.90/1.13      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.90/1.13  thf(t54_relat_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( v1_relat_1 @ A ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( v1_relat_1 @ B ) =>
% 0.90/1.13           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.90/1.13             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.90/1.13  thf('26', plain,
% 0.90/1.13      (![X13 : $i, X14 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X13)
% 0.90/1.13          | ((k4_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 0.90/1.13              = (k5_relat_1 @ (k4_relat_1 @ X13) @ (k4_relat_1 @ X14)))
% 0.90/1.13          | ~ (v1_relat_1 @ X14))),
% 0.90/1.13      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.90/1.13  thf('27', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 0.90/1.13            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X1)
% 0.90/1.13          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.90/1.13      inference('sup+', [status(thm)], ['25', '26'])).
% 0.90/1.13  thf('28', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X1)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 0.90/1.13              = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['24', '27'])).
% 0.90/1.13  thf('29', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 0.90/1.13            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 0.90/1.13          | ~ (v1_relat_1 @ X1)
% 0.90/1.13          | ~ (v1_relat_1 @ X0))),
% 0.90/1.13      inference('simplify', [status(thm)], ['28'])).
% 0.90/1.13  thf('30', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((k4_relat_1 @ k1_xboole_0)
% 0.90/1.13            = (k5_relat_1 @ X0 @ (k4_relat_1 @ k1_xboole_0)))
% 0.90/1.13          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.90/1.13      inference('sup+', [status(thm)], ['23', '29'])).
% 0.90/1.13  thf(t62_relat_1, conjecture,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( v1_relat_1 @ A ) =>
% 0.90/1.13       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.90/1.13         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.90/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.13    (~( ![A:$i]:
% 0.90/1.13        ( ( v1_relat_1 @ A ) =>
% 0.90/1.13          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.90/1.13            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.90/1.13    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.90/1.13  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('32', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.90/1.13      inference('demod', [status(thm)], ['19', '20'])).
% 0.90/1.13  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('34', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.90/1.13      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.90/1.13  thf('35', plain,
% 0.90/1.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.13  thf('36', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.13  thf('37', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.90/1.13          | ~ (v1_xboole_0 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X1))),
% 0.90/1.13      inference('sup+', [status(thm)], ['35', '36'])).
% 0.90/1.13  thf('38', plain,
% 0.90/1.13      (![X7 : $i, X8 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X7)
% 0.90/1.13          | ~ (v1_relat_1 @ X8)
% 0.90/1.13          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.90/1.13  thf('39', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         ((v1_relat_1 @ k1_xboole_0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_xboole_0 @ X1)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X1))),
% 0.90/1.13      inference('sup+', [status(thm)], ['37', '38'])).
% 0.90/1.13  thf('40', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X1)
% 0.90/1.13          | ~ (v1_xboole_0 @ X1)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | (v1_relat_1 @ k1_xboole_0))),
% 0.90/1.13      inference('simplify', [status(thm)], ['39'])).
% 0.90/1.13  thf('41', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (v1_xboole_0 @ X0)
% 0.90/1.13          | (v1_relat_1 @ k1_xboole_0)
% 0.90/1.13          | ~ (v1_relat_1 @ X1)
% 0.90/1.13          | ~ (v1_xboole_0 @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['34', '40'])).
% 0.90/1.13  thf('42', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X1)
% 0.90/1.13          | (v1_relat_1 @ k1_xboole_0)
% 0.90/1.13          | ~ (v1_xboole_0 @ X0))),
% 0.90/1.13      inference('simplify', [status(thm)], ['41'])).
% 0.90/1.13  thf('43', plain,
% 0.90/1.13      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['33', '42'])).
% 0.90/1.13  thf('44', plain,
% 0.90/1.13      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['32', '43'])).
% 0.90/1.13  thf('45', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.90/1.13      inference('sup-', [status(thm)], ['31', '44'])).
% 0.90/1.13  thf('46', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((k4_relat_1 @ k1_xboole_0)
% 0.90/1.13            = (k5_relat_1 @ X0 @ (k4_relat_1 @ k1_xboole_0)))
% 0.90/1.13          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.90/1.13          | ~ (v1_relat_1 @ X0))),
% 0.90/1.13      inference('demod', [status(thm)], ['30', '45'])).
% 0.90/1.13  thf('47', plain,
% 0.90/1.13      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.90/1.13  thf('48', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | ((k4_relat_1 @ k1_xboole_0)
% 0.90/1.13              = (k5_relat_1 @ X0 @ (k4_relat_1 @ k1_xboole_0))))),
% 0.90/1.13      inference('clc', [status(thm)], ['46', '47'])).
% 0.90/1.13  thf('49', plain,
% 0.90/1.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.13  thf('50', plain,
% 0.90/1.13      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.90/1.13        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('51', plain,
% 0.90/1.13      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.90/1.13         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.90/1.13      inference('split', [status(esa)], ['50'])).
% 0.90/1.13  thf('52', plain,
% 0.90/1.13      ((![X0 : $i]:
% 0.90/1.13          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.90/1.13         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['49', '51'])).
% 0.90/1.13  thf('53', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.90/1.13      inference('demod', [status(thm)], ['19', '20'])).
% 0.90/1.13  thf('54', plain,
% 0.90/1.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.13  thf('55', plain,
% 0.90/1.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.13  thf('56', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.90/1.13      inference('sup+', [status(thm)], ['54', '55'])).
% 0.90/1.13  thf('57', plain,
% 0.90/1.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.13  thf('58', plain,
% 0.90/1.13      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.90/1.13         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.90/1.13      inference('split', [status(esa)], ['50'])).
% 0.90/1.13  thf('59', plain,
% 0.90/1.13      ((![X0 : $i]:
% 0.90/1.13          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.90/1.13         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['57', '58'])).
% 0.90/1.13  thf('60', plain,
% 0.90/1.13      ((![X0 : $i, X1 : $i]:
% 0.90/1.13          (((X0) != (k1_xboole_0))
% 0.90/1.13           | ~ (v1_xboole_0 @ X0)
% 0.90/1.13           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.90/1.13           | ~ (v1_xboole_0 @ X1)))
% 0.90/1.13         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['56', '59'])).
% 0.90/1.13  thf('61', plain,
% 0.90/1.13      ((![X1 : $i]:
% 0.90/1.13          (~ (v1_xboole_0 @ X1)
% 0.90/1.13           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.90/1.13           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.90/1.13         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.90/1.13      inference('simplify', [status(thm)], ['60'])).
% 0.90/1.13  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.13      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.13  thf('63', plain,
% 0.90/1.13      ((![X1 : $i]:
% 0.90/1.13          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.90/1.13         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.90/1.13      inference('simplify_reflect+', [status(thm)], ['61', '62'])).
% 0.90/1.13  thf('64', plain,
% 0.90/1.13      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.90/1.13         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['53', '63'])).
% 0.90/1.13  thf('65', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.13      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.13  thf('67', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.90/1.13      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.90/1.13  thf('68', plain,
% 0.90/1.13      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.90/1.13       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.90/1.13      inference('split', [status(esa)], ['50'])).
% 0.90/1.13  thf('69', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.90/1.13      inference('sat_resolution*', [status(thm)], ['67', '68'])).
% 0.90/1.13  thf('70', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.13      inference('simpl_trail', [status(thm)], ['52', '69'])).
% 0.90/1.13  thf('71', plain,
% 0.90/1.13      ((((k4_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.90/1.13        | ~ (v1_relat_1 @ sk_A)
% 0.90/1.13        | ~ (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['48', '70'])).
% 0.90/1.13  thf('72', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('73', plain,
% 0.90/1.13      ((((k4_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.90/1.13        | ~ (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.90/1.13      inference('demod', [status(thm)], ['71', '72'])).
% 0.90/1.13  thf('74', plain,
% 0.90/1.13      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.90/1.13  thf('75', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.13  thf('76', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | ((k4_relat_1 @ k1_xboole_0)
% 0.90/1.13              = (k5_relat_1 @ X0 @ (k4_relat_1 @ k1_xboole_0))))),
% 0.90/1.13      inference('clc', [status(thm)], ['46', '47'])).
% 0.90/1.13  thf('77', plain,
% 0.90/1.13      ((((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.90/1.13        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 0.90/1.13        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.90/1.13      inference('sup+', [status(thm)], ['75', '76'])).
% 0.90/1.13  thf('78', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.90/1.13      inference('sup-', [status(thm)], ['31', '44'])).
% 0.90/1.13  thf('79', plain,
% 0.90/1.13      ((((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.90/1.13        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.90/1.14      inference('demod', [status(thm)], ['77', '78'])).
% 0.90/1.14  thf('80', plain,
% 0.90/1.14      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.90/1.14        | ((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['74', '79'])).
% 0.90/1.14  thf('81', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.90/1.14      inference('sup-', [status(thm)], ['31', '44'])).
% 0.90/1.14  thf('82', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.14      inference('demod', [status(thm)], ['80', '81'])).
% 0.90/1.14  thf('83', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.14      inference('demod', [status(thm)], ['80', '81'])).
% 0.90/1.14  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.14  thf('85', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.90/1.14      inference('demod', [status(thm)], ['73', '82', '83', '84'])).
% 0.90/1.14  thf('86', plain, ($false), inference('simplify', [status(thm)], ['85'])).
% 0.90/1.14  
% 0.90/1.14  % SZS output end Refutation
% 0.90/1.14  
% 0.90/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
