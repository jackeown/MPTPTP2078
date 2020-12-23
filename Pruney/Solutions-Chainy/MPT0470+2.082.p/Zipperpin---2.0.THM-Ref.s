%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a7in1JSjaX

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:38 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 278 expanded)
%              Number of leaves         :   19 (  91 expanded)
%              Depth                    :   29
%              Number of atoms          :  671 (1817 expanded)
%              Number of equality atoms :   47 ( 120 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X2: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf('47',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','37'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('54',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('66',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('77',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['62','77'])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['79','80','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a7in1JSjaX
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:49:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 424 iterations in 0.201s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(dt_k5_relat_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.46/0.66       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X3)
% 0.46/0.66          | ~ (v1_relat_1 @ X4)
% 0.46/0.66          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.46/0.66  thf(t60_relat_1, axiom,
% 0.46/0.66    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.46/0.66     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.66  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.46/0.66  thf(t45_relat_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( v1_relat_1 @ B ) =>
% 0.46/0.66           ( r1_tarski @
% 0.46/0.66             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X9)
% 0.46/0.66          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X10 @ X9)) @ 
% 0.46/0.66             (k2_relat_1 @ X9))
% 0.46/0.66          | ~ (v1_relat_1 @ X10))),
% 0.46/0.66      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.46/0.66           k1_xboole_0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf(t62_relat_1, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ A ) =>
% 0.46/0.66       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.46/0.66         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( v1_relat_1 @ A ) =>
% 0.46/0.66          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.46/0.66            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.46/0.66  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(cc1_relat_1, axiom,
% 0.46/0.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.46/0.66  thf('5', plain, (![X2 : $i]: ((v1_relat_1 @ X2) | ~ (v1_xboole_0 @ X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X3)
% 0.46/0.66          | ~ (v1_relat_1 @ X4)
% 0.46/0.66          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.46/0.66  thf('7', plain, (![X2 : $i]: ((v1_relat_1 @ X2) | ~ (v1_xboole_0 @ X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.46/0.66  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.46/0.66  thf(t44_relat_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( v1_relat_1 @ B ) =>
% 0.46/0.66           ( r1_tarski @
% 0.46/0.66             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X7)
% 0.46/0.66          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X8 @ X7)) @ 
% 0.46/0.66             (k1_relat_1 @ X8))
% 0.46/0.66          | ~ (v1_relat_1 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.46/0.66           k1_xboole_0)
% 0.46/0.66          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.46/0.66             k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['7', '10'])).
% 0.46/0.66  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.66  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.46/0.66             k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf(t3_xboole_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.66  thf(fc8_relat_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.46/0.66       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X5 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ (k1_relat_1 @ X5))
% 0.46/0.66          | ~ (v1_relat_1 @ X5)
% 0.46/0.66          | (v1_xboole_0 @ X5))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.66  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['17', '18'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.66          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['6', '19'])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['5', '21'])).
% 0.46/0.66  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf('25', plain, (![X2 : $i]: ((v1_relat_1 @ X2) | ~ (v1_xboole_0 @ X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.46/0.66  thf(l13_xboole_0, axiom,
% 0.46/0.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.66          | ~ (v1_xboole_0 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['26', '29'])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X3)
% 0.46/0.66          | ~ (v1_relat_1 @ X4)
% 0.46/0.66          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((v1_relat_1 @ k1_xboole_0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_xboole_0 @ X1)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X1)
% 0.46/0.66          | ~ (v1_xboole_0 @ X1)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v1_relat_1 @ k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ X0)
% 0.46/0.66          | (v1_relat_1 @ k1_xboole_0)
% 0.46/0.66          | ~ (v1_relat_1 @ X1)
% 0.46/0.66          | ~ (v1_xboole_0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['25', '33'])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X1)
% 0.46/0.66          | (v1_relat_1 @ k1_xboole_0)
% 0.46/0.66          | ~ (v1_xboole_0 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['34'])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v1_relat_1 @ k1_xboole_0)
% 0.46/0.66          | ~ (v1_relat_1 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['24', '35'])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.46/0.66      inference('condensation', [status(thm)], ['36'])).
% 0.46/0.66  thf('38', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '37'])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.46/0.66           k1_xboole_0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['3', '38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.66  thf(fc9_relat_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.46/0.66       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X6 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ (k2_relat_1 @ X6))
% 0.46/0.66          | ~ (v1_relat_1 @ X6)
% 0.46/0.66          | (v1_xboole_0 @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.46/0.66          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.66  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.46/0.66          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '45'])).
% 0.46/0.66  thf('47', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '37'])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['48'])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.46/0.66        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.46/0.66         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['54'])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          (((X0) != (k1_xboole_0))
% 0.46/0.66           | ~ (v1_xboole_0 @ X0)
% 0.46/0.66           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.46/0.66         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['53', '55'])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.46/0.66         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.46/0.66         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['56'])).
% 0.46/0.66  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 0.46/0.66         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.46/0.66      inference('simplify_reflect+', [status(thm)], ['57', '58'])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0))
% 0.46/0.66           | ~ (v1_xboole_0 @ X0)
% 0.46/0.66           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.46/0.66         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['52', '59'])).
% 0.46/0.66  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.46/0.66         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.46/0.66      inference('demod', [status(thm)], ['60', '61'])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.46/0.66         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['54'])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.46/0.66         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      ((![X0 : $i, X1 : $i]:
% 0.46/0.66          (((X0) != (k1_xboole_0))
% 0.46/0.66           | ~ (v1_xboole_0 @ X0)
% 0.46/0.66           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.46/0.66           | ~ (v1_xboole_0 @ X1)))
% 0.46/0.66         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['64', '67'])).
% 0.46/0.66  thf('69', plain,
% 0.46/0.66      ((![X1 : $i]:
% 0.46/0.66          (~ (v1_xboole_0 @ X1)
% 0.46/0.66           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.46/0.66           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.46/0.66         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['68'])).
% 0.46/0.66  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      ((![X1 : $i]:
% 0.46/0.66          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.46/0.66         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('simplify_reflect+', [status(thm)], ['69', '70'])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.46/0.66         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['63', '71'])).
% 0.46/0.66  thf('73', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.66  thf('75', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.46/0.66  thf('76', plain,
% 0.46/0.66      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.46/0.66       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('split', [status(esa)], ['54'])).
% 0.46/0.66  thf('77', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['75', '76'])).
% 0.46/0.66  thf('78', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['62', '77'])).
% 0.46/0.66  thf('79', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['49', '78'])).
% 0.46/0.66  thf('80', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.66  thf('82', plain, ($false),
% 0.46/0.66      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.53/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
