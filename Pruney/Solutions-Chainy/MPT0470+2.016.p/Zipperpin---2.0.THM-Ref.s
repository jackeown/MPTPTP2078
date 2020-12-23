%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vC9GiObg4J

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:28 EST 2020

% Result     : Theorem 0.93s
% Output     : Refutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 588 expanded)
%              Number of leaves         :   22 ( 190 expanded)
%              Depth                    :   27
%              Number of atoms          :  718 (3898 expanded)
%              Number of equality atoms :   61 ( 230 expanded)
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

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
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
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
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
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
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
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ X0 ) )
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
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
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
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
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
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
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
        = ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ X0 ) )
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
        = ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ X0 ) ) ) ),
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
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
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
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('69',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A )
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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('79',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','44'])).

thf('81',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','44'])).

thf('84',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['75','84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vC9GiObg4J
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:57 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.93/1.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.93/1.09  % Solved by: fo/fo7.sh
% 0.93/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.93/1.09  % done 1103 iterations in 0.627s
% 0.93/1.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.93/1.09  % SZS output start Refutation
% 0.93/1.09  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.93/1.09  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.93/1.09  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.93/1.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.93/1.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.93/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.93/1.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.93/1.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.93/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.93/1.09  thf(cc1_relat_1, axiom,
% 0.93/1.09    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.93/1.09  thf('0', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.93/1.09      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.93/1.09  thf(dt_k5_relat_1, axiom,
% 0.93/1.09    (![A:$i,B:$i]:
% 0.93/1.09     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.93/1.09       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.93/1.09  thf('1', plain,
% 0.93/1.09      (![X7 : $i, X8 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X7)
% 0.93/1.09          | ~ (v1_relat_1 @ X8)
% 0.93/1.09          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.93/1.09      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.93/1.09  thf('2', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.93/1.09      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.93/1.09  thf(t60_relat_1, axiom,
% 0.93/1.09    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.93/1.09     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.93/1.09  thf('3', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.93/1.09      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.93/1.09  thf(t45_relat_1, axiom,
% 0.93/1.09    (![A:$i]:
% 0.93/1.09     ( ( v1_relat_1 @ A ) =>
% 0.93/1.09       ( ![B:$i]:
% 0.93/1.09         ( ( v1_relat_1 @ B ) =>
% 0.93/1.09           ( r1_tarski @
% 0.93/1.09             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.93/1.09  thf('4', plain,
% 0.93/1.09      (![X11 : $i, X12 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X11)
% 0.93/1.09          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X12 @ X11)) @ 
% 0.93/1.09             (k2_relat_1 @ X11))
% 0.93/1.09          | ~ (v1_relat_1 @ X12))),
% 0.93/1.09      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.93/1.09  thf('5', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.93/1.09           k1_xboole_0)
% 0.93/1.09          | ~ (v1_relat_1 @ X0)
% 0.93/1.09          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.93/1.09      inference('sup+', [status(thm)], ['3', '4'])).
% 0.93/1.09  thf('6', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.93/1.09          | ~ (v1_relat_1 @ X0)
% 0.93/1.09          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.93/1.09             k1_xboole_0))),
% 0.93/1.09      inference('sup-', [status(thm)], ['2', '5'])).
% 0.93/1.09  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.93/1.09  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.93/1.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.93/1.09  thf('8', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X0)
% 0.93/1.09          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.93/1.09             k1_xboole_0))),
% 0.93/1.09      inference('demod', [status(thm)], ['6', '7'])).
% 0.93/1.09  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.93/1.09  thf('9', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.93/1.09      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.93/1.09  thf(d10_xboole_0, axiom,
% 0.93/1.09    (![A:$i,B:$i]:
% 0.93/1.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.93/1.09  thf('10', plain,
% 0.93/1.09      (![X1 : $i, X3 : $i]:
% 0.93/1.09         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.93/1.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.93/1.09  thf('11', plain,
% 0.93/1.09      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.93/1.09      inference('sup-', [status(thm)], ['9', '10'])).
% 0.93/1.09  thf('12', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X0)
% 0.93/1.09          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.93/1.09      inference('sup-', [status(thm)], ['8', '11'])).
% 0.93/1.09  thf(fc9_relat_1, axiom,
% 0.93/1.09    (![A:$i]:
% 0.93/1.09     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.93/1.09       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.93/1.09  thf('13', plain,
% 0.93/1.09      (![X9 : $i]:
% 0.93/1.09         (~ (v1_xboole_0 @ (k2_relat_1 @ X9))
% 0.93/1.09          | ~ (v1_relat_1 @ X9)
% 0.93/1.09          | (v1_xboole_0 @ X9))),
% 0.93/1.09      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.93/1.09  thf('14', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.93/1.09          | ~ (v1_relat_1 @ X0)
% 0.93/1.09          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.93/1.09          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.93/1.09      inference('sup-', [status(thm)], ['12', '13'])).
% 0.93/1.09  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.93/1.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.93/1.09  thf('16', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X0)
% 0.93/1.09          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.93/1.09          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.93/1.09      inference('demod', [status(thm)], ['14', '15'])).
% 0.93/1.09  thf('17', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ k1_xboole_0)
% 0.93/1.09          | ~ (v1_relat_1 @ X0)
% 0.93/1.09          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.93/1.09          | ~ (v1_relat_1 @ X0))),
% 0.93/1.09      inference('sup-', [status(thm)], ['1', '16'])).
% 0.93/1.09  thf('18', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.93/1.09          | ~ (v1_relat_1 @ X0)
% 0.93/1.09          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.93/1.09      inference('simplify', [status(thm)], ['17'])).
% 0.93/1.09  thf('19', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.93/1.09          | ~ (v1_relat_1 @ X0)
% 0.93/1.09          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.93/1.09      inference('sup-', [status(thm)], ['0', '18'])).
% 0.93/1.09  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.93/1.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.93/1.09  thf('21', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.93/1.09      inference('demod', [status(thm)], ['19', '20'])).
% 0.93/1.09  thf(l13_xboole_0, axiom,
% 0.93/1.09    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.93/1.09  thf('22', plain,
% 0.93/1.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.93/1.09      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.93/1.09  thf('23', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X0)
% 0.93/1.09          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.93/1.09      inference('sup-', [status(thm)], ['21', '22'])).
% 0.93/1.09  thf(dt_k4_relat_1, axiom,
% 0.93/1.09    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.93/1.09  thf('24', plain,
% 0.93/1.09      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.93/1.09      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.93/1.09  thf(involutiveness_k4_relat_1, axiom,
% 0.93/1.09    (![A:$i]:
% 0.93/1.09     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.93/1.09  thf('25', plain,
% 0.93/1.09      (![X10 : $i]:
% 0.93/1.09         (((k4_relat_1 @ (k4_relat_1 @ X10)) = (X10)) | ~ (v1_relat_1 @ X10))),
% 0.93/1.09      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.93/1.09  thf(t54_relat_1, axiom,
% 0.93/1.09    (![A:$i]:
% 0.93/1.09     ( ( v1_relat_1 @ A ) =>
% 0.93/1.09       ( ![B:$i]:
% 0.93/1.09         ( ( v1_relat_1 @ B ) =>
% 0.93/1.09           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.93/1.09             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.93/1.09  thf('26', plain,
% 0.93/1.09      (![X13 : $i, X14 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X13)
% 0.93/1.09          | ((k4_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 0.93/1.09              = (k5_relat_1 @ (k4_relat_1 @ X13) @ (k4_relat_1 @ X14)))
% 0.93/1.09          | ~ (v1_relat_1 @ X14))),
% 0.93/1.09      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.93/1.09  thf('27', plain,
% 0.93/1.09      (![X0 : $i, X1 : $i]:
% 0.93/1.09         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 0.93/1.09            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 0.93/1.09          | ~ (v1_relat_1 @ X0)
% 0.93/1.09          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.93/1.09          | ~ (v1_relat_1 @ X1))),
% 0.93/1.09      inference('sup+', [status(thm)], ['25', '26'])).
% 0.93/1.09  thf('28', plain,
% 0.93/1.09      (![X0 : $i, X1 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X0)
% 0.93/1.09          | ~ (v1_relat_1 @ X1)
% 0.93/1.09          | ~ (v1_relat_1 @ X0)
% 0.93/1.09          | ((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 0.93/1.09              = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0)))),
% 0.93/1.09      inference('sup-', [status(thm)], ['24', '27'])).
% 0.93/1.09  thf('29', plain,
% 0.93/1.09      (![X0 : $i, X1 : $i]:
% 0.93/1.09         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 0.93/1.09            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 0.93/1.09          | ~ (v1_relat_1 @ X1)
% 0.93/1.09          | ~ (v1_relat_1 @ X0))),
% 0.93/1.09      inference('simplify', [status(thm)], ['28'])).
% 0.93/1.09  thf('30', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (((k4_relat_1 @ k1_xboole_0)
% 0.93/1.09            = (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ X0))
% 0.93/1.09          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.93/1.09          | ~ (v1_relat_1 @ X0)
% 0.93/1.09          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.93/1.09      inference('sup+', [status(thm)], ['23', '29'])).
% 0.93/1.09  thf(t62_relat_1, conjecture,
% 0.93/1.09    (![A:$i]:
% 0.93/1.09     ( ( v1_relat_1 @ A ) =>
% 0.93/1.09       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.93/1.09         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.93/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.93/1.09    (~( ![A:$i]:
% 0.93/1.09        ( ( v1_relat_1 @ A ) =>
% 0.93/1.09          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.93/1.09            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.93/1.09    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.93/1.09  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.93/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.09  thf('32', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.93/1.09      inference('demod', [status(thm)], ['19', '20'])).
% 0.93/1.09  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.93/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.09  thf('34', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.93/1.09      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.93/1.09  thf('35', plain,
% 0.93/1.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.93/1.09      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.93/1.09  thf('36', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X0)
% 0.93/1.09          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.93/1.09      inference('sup-', [status(thm)], ['21', '22'])).
% 0.93/1.09  thf('37', plain,
% 0.93/1.09      (![X0 : $i, X1 : $i]:
% 0.93/1.09         (((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.93/1.09          | ~ (v1_xboole_0 @ X0)
% 0.93/1.09          | ~ (v1_relat_1 @ X1))),
% 0.93/1.09      inference('sup+', [status(thm)], ['35', '36'])).
% 0.93/1.09  thf('38', plain,
% 0.93/1.09      (![X7 : $i, X8 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X7)
% 0.93/1.09          | ~ (v1_relat_1 @ X8)
% 0.93/1.09          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.93/1.09      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.93/1.09  thf('39', plain,
% 0.93/1.09      (![X0 : $i, X1 : $i]:
% 0.93/1.09         ((v1_relat_1 @ k1_xboole_0)
% 0.93/1.09          | ~ (v1_relat_1 @ X1)
% 0.93/1.09          | ~ (v1_xboole_0 @ X0)
% 0.93/1.09          | ~ (v1_relat_1 @ X0)
% 0.93/1.09          | ~ (v1_relat_1 @ X1))),
% 0.93/1.09      inference('sup+', [status(thm)], ['37', '38'])).
% 0.93/1.09  thf('40', plain,
% 0.93/1.09      (![X0 : $i, X1 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X0)
% 0.93/1.09          | ~ (v1_xboole_0 @ X0)
% 0.93/1.09          | ~ (v1_relat_1 @ X1)
% 0.93/1.09          | (v1_relat_1 @ k1_xboole_0))),
% 0.93/1.09      inference('simplify', [status(thm)], ['39'])).
% 0.93/1.09  thf('41', plain,
% 0.93/1.09      (![X0 : $i, X1 : $i]:
% 0.93/1.09         (~ (v1_xboole_0 @ X0)
% 0.93/1.09          | (v1_relat_1 @ k1_xboole_0)
% 0.93/1.09          | ~ (v1_relat_1 @ X1)
% 0.93/1.09          | ~ (v1_xboole_0 @ X0))),
% 0.93/1.09      inference('sup-', [status(thm)], ['34', '40'])).
% 0.93/1.09  thf('42', plain,
% 0.93/1.09      (![X0 : $i, X1 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X1)
% 0.93/1.09          | (v1_relat_1 @ k1_xboole_0)
% 0.93/1.09          | ~ (v1_xboole_0 @ X0))),
% 0.93/1.09      inference('simplify', [status(thm)], ['41'])).
% 0.93/1.09  thf('43', plain,
% 0.93/1.09      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.93/1.09      inference('sup-', [status(thm)], ['33', '42'])).
% 0.93/1.09  thf('44', plain,
% 0.93/1.09      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.93/1.09      inference('sup-', [status(thm)], ['32', '43'])).
% 0.93/1.09  thf('45', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.93/1.09      inference('sup-', [status(thm)], ['31', '44'])).
% 0.93/1.09  thf('46', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (((k4_relat_1 @ k1_xboole_0)
% 0.93/1.09            = (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ X0))
% 0.93/1.09          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.93/1.09          | ~ (v1_relat_1 @ X0))),
% 0.93/1.09      inference('demod', [status(thm)], ['30', '45'])).
% 0.93/1.09  thf('47', plain,
% 0.93/1.09      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.93/1.09      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.93/1.09  thf('48', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X0)
% 0.93/1.09          | ((k4_relat_1 @ k1_xboole_0)
% 0.93/1.09              = (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ X0)))),
% 0.93/1.09      inference('clc', [status(thm)], ['46', '47'])).
% 0.93/1.09  thf('49', plain,
% 0.93/1.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.93/1.09      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.93/1.09  thf('50', plain,
% 0.93/1.09      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.93/1.09        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.93/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.09  thf('51', plain,
% 0.93/1.09      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.93/1.09         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.93/1.09      inference('split', [status(esa)], ['50'])).
% 0.93/1.09  thf('52', plain,
% 0.93/1.09      ((![X0 : $i]:
% 0.93/1.09          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.93/1.09         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.93/1.09      inference('sup-', [status(thm)], ['49', '51'])).
% 0.93/1.09  thf('53', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.93/1.09      inference('demod', [status(thm)], ['19', '20'])).
% 0.93/1.09  thf('54', plain,
% 0.93/1.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.93/1.09      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.93/1.09  thf('55', plain,
% 0.93/1.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.93/1.09      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.93/1.09  thf('56', plain,
% 0.93/1.09      (![X0 : $i, X1 : $i]:
% 0.93/1.09         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.93/1.09      inference('sup+', [status(thm)], ['54', '55'])).
% 0.93/1.09  thf('57', plain,
% 0.93/1.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.93/1.09      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.93/1.09  thf('58', plain,
% 0.93/1.09      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.93/1.09         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.93/1.09      inference('split', [status(esa)], ['50'])).
% 0.93/1.09  thf('59', plain,
% 0.93/1.09      ((![X0 : $i]:
% 0.93/1.09          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.93/1.09         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.93/1.09      inference('sup-', [status(thm)], ['57', '58'])).
% 0.93/1.09  thf('60', plain,
% 0.93/1.09      ((![X0 : $i, X1 : $i]:
% 0.93/1.09          (((X0) != (k1_xboole_0))
% 0.93/1.09           | ~ (v1_xboole_0 @ X0)
% 0.93/1.09           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.93/1.09           | ~ (v1_xboole_0 @ X1)))
% 0.93/1.09         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.93/1.09      inference('sup-', [status(thm)], ['56', '59'])).
% 0.93/1.09  thf('61', plain,
% 0.93/1.09      ((![X1 : $i]:
% 0.93/1.09          (~ (v1_xboole_0 @ X1)
% 0.93/1.09           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.93/1.09           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.93/1.09         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.93/1.09      inference('simplify', [status(thm)], ['60'])).
% 0.93/1.09  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.93/1.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.93/1.09  thf('63', plain,
% 0.93/1.09      ((![X1 : $i]:
% 0.93/1.09          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))))
% 0.93/1.09         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.93/1.09      inference('simplify_reflect+', [status(thm)], ['61', '62'])).
% 0.93/1.09  thf('64', plain,
% 0.93/1.09      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.93/1.09         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.93/1.09      inference('sup-', [status(thm)], ['53', '63'])).
% 0.93/1.09  thf('65', plain, ((v1_relat_1 @ sk_A)),
% 0.93/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.09  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.93/1.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.93/1.09  thf('67', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.93/1.09      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.93/1.09  thf('68', plain,
% 0.93/1.09      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 0.93/1.09       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.93/1.09      inference('split', [status(esa)], ['50'])).
% 0.93/1.09  thf('69', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.93/1.09      inference('sat_resolution*', [status(thm)], ['67', '68'])).
% 0.93/1.09  thf('70', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.93/1.09      inference('simpl_trail', [status(thm)], ['52', '69'])).
% 0.93/1.09  thf('71', plain,
% 0.93/1.09      ((((k4_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.93/1.09        | ~ (v1_relat_1 @ sk_A)
% 0.93/1.09        | ~ (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.93/1.09      inference('sup-', [status(thm)], ['48', '70'])).
% 0.93/1.09  thf('72', plain, ((v1_relat_1 @ sk_A)),
% 0.93/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.09  thf('73', plain,
% 0.93/1.09      ((((k4_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.93/1.09        | ~ (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.93/1.09      inference('demod', [status(thm)], ['71', '72'])).
% 0.93/1.09  thf('74', plain,
% 0.93/1.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.93/1.09      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.93/1.09  thf('75', plain, (~ (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0))),
% 0.93/1.09      inference('clc', [status(thm)], ['73', '74'])).
% 0.93/1.09  thf('76', plain,
% 0.93/1.09      (![X6 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.93/1.09      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.93/1.09  thf('77', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X0)
% 0.93/1.09          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.93/1.09      inference('sup-', [status(thm)], ['21', '22'])).
% 0.93/1.09  thf('78', plain,
% 0.93/1.09      (![X0 : $i]:
% 0.93/1.09         (~ (v1_relat_1 @ X0)
% 0.93/1.09          | ((k4_relat_1 @ k1_xboole_0)
% 0.93/1.09              = (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ X0)))),
% 0.93/1.09      inference('clc', [status(thm)], ['46', '47'])).
% 0.93/1.09  thf('79', plain,
% 0.93/1.09      ((((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.93/1.09        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 0.93/1.09        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.93/1.09      inference('sup+', [status(thm)], ['77', '78'])).
% 0.93/1.09  thf('80', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.93/1.09      inference('sup-', [status(thm)], ['31', '44'])).
% 0.93/1.09  thf('81', plain,
% 0.93/1.09      ((((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.93/1.09        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.93/1.09      inference('demod', [status(thm)], ['79', '80'])).
% 0.93/1.09  thf('82', plain,
% 0.93/1.09      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.93/1.09        | ((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.93/1.09      inference('sup-', [status(thm)], ['76', '81'])).
% 0.93/1.09  thf('83', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.93/1.09      inference('sup-', [status(thm)], ['31', '44'])).
% 0.93/1.09  thf('84', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.93/1.09      inference('demod', [status(thm)], ['82', '83'])).
% 0.93/1.09  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.93/1.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.93/1.09  thf('86', plain, ($false),
% 0.93/1.09      inference('demod', [status(thm)], ['75', '84', '85'])).
% 0.93/1.09  
% 0.93/1.09  % SZS output end Refutation
% 0.93/1.09  
% 0.93/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
