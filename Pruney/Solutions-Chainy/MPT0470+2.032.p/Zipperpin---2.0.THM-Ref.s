%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZmTT2wUiUa

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 122 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  600 ( 801 expanded)
%              Number of equality atoms :   46 (  76 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
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

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

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

thf('24',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('32',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('33',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('54',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('65',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['29','65'])).

thf('67',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZmTT2wUiUa
% 0.13/0.36  % Computer   : n018.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 13:50:42 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 170 iterations in 0.115s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(cc1_relat_1, axiom,
% 0.21/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.58  thf('0', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.58  thf(dt_k5_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.58       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X6)
% 0.21/0.58          | ~ (v1_relat_1 @ X7)
% 0.21/0.58          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.58  thf('2', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.58  thf(t60_relat_1, axiom,
% 0.21/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.58  thf('3', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.58  thf(t47_relat_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( v1_relat_1 @ B ) =>
% 0.21/0.58           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.58             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      (![X12 : $i, X13 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X12)
% 0.21/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X12 @ X13)) = (k2_relat_1 @ X13))
% 0.21/0.58          | ~ (r1_tarski @ (k1_relat_1 @ X13) @ (k2_relat_1 @ X12))
% 0.21/0.58          | ~ (v1_relat_1 @ X13))),
% 0.21/0.58      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.58              = (k2_relat_1 @ k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.58  thf('6', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.58  thf('7', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['2', '8'])).
% 0.21/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.58  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf(fc9_relat_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.21/0.58       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (![X9 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ (k2_relat_1 @ X9))
% 0.21/0.58          | ~ (v1_relat_1 @ X9)
% 0.21/0.58          | (v1_xboole_0 @ X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.58  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['1', '15'])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['0', '17'])).
% 0.21/0.58  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf(l13_xboole_0, axiom,
% 0.21/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.58      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.58  thf(t62_relat_1, conjecture,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ A ) =>
% 0.21/0.58       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.58         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i]:
% 0.21/0.58        ( ( v1_relat_1 @ A ) =>
% 0.21/0.58          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.58            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.21/0.58        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.58      inference('split', [status(esa)], ['24'])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      ((![X0 : $i]:
% 0.21/0.58          (((X0) != (k1_xboole_0))
% 0.21/0.58           | ~ (v1_xboole_0 @ X0)
% 0.21/0.58           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.21/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['23', '25'])).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      (((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.21/0.58         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.21/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.58      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.58  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 0.21/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.58      inference('simplify_reflect+', [status(thm)], ['27', '28'])).
% 0.21/0.58  thf('30', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X6)
% 0.21/0.58          | ~ (v1_relat_1 @ X7)
% 0.21/0.58          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.58  thf('32', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.58  thf('33', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.58  thf(t44_relat_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( v1_relat_1 @ B ) =>
% 0.21/0.58           ( r1_tarski @
% 0.21/0.58             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      (![X10 : $i, X11 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X10)
% 0.21/0.58          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 0.21/0.58             (k1_relat_1 @ X11))
% 0.21/0.58          | ~ (v1_relat_1 @ X11))),
% 0.21/0.58      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.21/0.58           k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.21/0.58             k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['32', '35'])).
% 0.21/0.58  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.21/0.58             k1_xboole_0))),
% 0.21/0.58      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.58  thf('39', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.58  thf(d10_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (![X1 : $i, X3 : $i]:
% 0.21/0.58         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['38', '41'])).
% 0.21/0.58  thf(fc8_relat_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.21/0.58       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.21/0.58  thf('43', plain,
% 0.21/0.58      (![X8 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ (k1_relat_1 @ X8))
% 0.21/0.58          | ~ (v1_relat_1 @ X8)
% 0.21/0.58          | (v1_xboole_0 @ X8))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.21/0.58  thf('44', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.58  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.58          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['31', '46'])).
% 0.21/0.58  thf('48', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['30', '48'])).
% 0.21/0.58  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('51', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.58      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.58  thf('53', plain,
% 0.21/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.58  thf('54', plain,
% 0.21/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.21/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('split', [status(esa)], ['24'])).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      ((![X0 : $i]:
% 0.21/0.58          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.21/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.58  thf('56', plain,
% 0.21/0.58      ((![X0 : $i, X1 : $i]:
% 0.21/0.58          (((X0) != (k1_xboole_0))
% 0.21/0.58           | ~ (v1_xboole_0 @ X0)
% 0.21/0.58           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.21/0.58           | ~ (v1_xboole_0 @ X1)))
% 0.21/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['52', '55'])).
% 0.21/0.58  thf('57', plain,
% 0.21/0.58      ((![X1 : $i]:
% 0.21/0.58          (~ (v1_xboole_0 @ X1)
% 0.21/0.58           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.21/0.58           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.21/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.58  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('59', plain,
% 0.21/0.58      ((![X1 : $i]:
% 0.21/0.58          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.21/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('simplify_reflect+', [status(thm)], ['57', '58'])).
% 0.21/0.58  thf('60', plain,
% 0.21/0.58      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.21/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['51', '59'])).
% 0.21/0.58  thf('61', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('63', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.21/0.58       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.58      inference('split', [status(esa)], ['24'])).
% 0.21/0.58  thf('65', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 0.21/0.58  thf('66', plain, (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['29', '65'])).
% 0.21/0.58  thf('67', plain, (~ (v1_relat_1 @ sk_A)),
% 0.21/0.58      inference('sup-', [status(thm)], ['20', '66'])).
% 0.21/0.58  thf('68', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('69', plain, ($false), inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
