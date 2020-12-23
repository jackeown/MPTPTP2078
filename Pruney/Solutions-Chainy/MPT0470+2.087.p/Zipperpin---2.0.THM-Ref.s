%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Tc0b7BjfZN

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:39 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 284 expanded)
%              Number of leaves         :   19 (  93 expanded)
%              Depth                    :   29
%              Number of atoms          :  672 (1843 expanded)
%              Number of equality atoms :   46 ( 116 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X3: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
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
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
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
    ! [X3: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['38'])).

thf('40',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','47'])).

thf('49',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','39'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('53',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

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
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
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
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

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
    inference('sup-',[status(thm)],['51','78'])).

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
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Tc0b7BjfZN
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 423 iterations in 0.204s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.66  thf(dt_k5_relat_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.47/0.66       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X4)
% 0.47/0.66          | ~ (v1_relat_1 @ X5)
% 0.47/0.66          | (v1_relat_1 @ (k5_relat_1 @ X4 @ X5)))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.47/0.66  thf(t60_relat_1, axiom,
% 0.47/0.66    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.47/0.66     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.66  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.66  thf(t45_relat_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( v1_relat_1 @ B ) =>
% 0.47/0.66           ( r1_tarski @
% 0.47/0.66             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (![X10 : $i, X11 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X10)
% 0.47/0.66          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 0.47/0.66             (k2_relat_1 @ X10))
% 0.47/0.66          | ~ (v1_relat_1 @ X11))),
% 0.47/0.66      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.47/0.66           k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X0)
% 0.47/0.66          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['1', '2'])).
% 0.47/0.66  thf(t62_relat_1, conjecture,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.47/0.66         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i]:
% 0.47/0.66        ( ( v1_relat_1 @ A ) =>
% 0.47/0.66          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.47/0.66            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.47/0.66  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(cc1_relat_1, axiom,
% 0.47/0.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.47/0.66  thf('5', plain, (![X3 : $i]: ((v1_relat_1 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X4)
% 0.47/0.66          | ~ (v1_relat_1 @ X5)
% 0.47/0.66          | (v1_relat_1 @ (k5_relat_1 @ X4 @ X5)))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.47/0.66  thf('7', plain, (![X3 : $i]: ((v1_relat_1 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.47/0.66  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.66  thf(t44_relat_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( v1_relat_1 @ B ) =>
% 0.47/0.66           ( r1_tarski @
% 0.47/0.66             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      (![X8 : $i, X9 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X8)
% 0.47/0.66          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X9 @ X8)) @ 
% 0.47/0.66             (k1_relat_1 @ X9))
% 0.47/0.66          | ~ (v1_relat_1 @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.47/0.66           k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['8', '9'])).
% 0.47/0.66  thf('11', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X0)
% 0.47/0.66          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.47/0.66             k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['7', '10'])).
% 0.47/0.66  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.66  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0)
% 0.47/0.66          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.47/0.66             k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.66  thf(t3_xboole_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0)
% 0.47/0.66          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.66  thf(fc8_relat_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.47/0.66       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X6 : $i]:
% 0.47/0.66         (~ (v1_xboole_0 @ (k1_relat_1 @ X6))
% 0.47/0.66          | ~ (v1_relat_1 @ X6)
% 0.47/0.66          | (v1_xboole_0 @ X6))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X0)
% 0.47/0.66          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.66          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.66  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0)
% 0.47/0.66          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.66          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0)
% 0.47/0.66          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.66          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.66          | ~ (v1_relat_1 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['6', '19'])).
% 0.47/0.66  thf('21', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.66          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['20'])).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X0)
% 0.47/0.66          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['5', '21'])).
% 0.47/0.66  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.66  thf('25', plain, (![X3 : $i]: ((v1_relat_1 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.47/0.66  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.66  thf(t8_boole, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.47/0.66  thf('27', plain,
% 0.47/0.66      (![X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t8_boole])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0)
% 0.47/0.66          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.47/0.66          | ~ (v1_xboole_0 @ X0)
% 0.47/0.66          | ~ (v1_relat_1 @ X1))),
% 0.47/0.66      inference('sup+', [status(thm)], ['28', '31'])).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X4)
% 0.47/0.66          | ~ (v1_relat_1 @ X5)
% 0.47/0.66          | (v1_relat_1 @ (k5_relat_1 @ X4 @ X5)))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v1_relat_1 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X0)
% 0.47/0.66          | ~ (v1_xboole_0 @ X1)
% 0.47/0.66          | ~ (v1_relat_1 @ X0)
% 0.47/0.66          | ~ (v1_relat_1 @ X1))),
% 0.47/0.66      inference('sup+', [status(thm)], ['32', '33'])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X1)
% 0.47/0.66          | ~ (v1_xboole_0 @ X1)
% 0.47/0.66          | ~ (v1_relat_1 @ X0)
% 0.47/0.66          | (v1_relat_1 @ k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['34'])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (v1_xboole_0 @ X0)
% 0.47/0.66          | (v1_relat_1 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X1)
% 0.47/0.66          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['25', '35'])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X1)
% 0.47/0.66          | (v1_relat_1 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['36'])).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0)
% 0.47/0.66          | (v1_relat_1 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['24', '37'])).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.47/0.66      inference('condensation', [status(thm)], ['38'])).
% 0.47/0.66  thf('40', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.66      inference('sup-', [status(thm)], ['4', '39'])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.47/0.66           k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['3', '40'])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.47/0.66  thf('43', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0)
% 0.47/0.66          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.66  thf(fc9_relat_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.47/0.66       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      (![X7 : $i]:
% 0.47/0.66         (~ (v1_xboole_0 @ (k2_relat_1 @ X7))
% 0.47/0.66          | ~ (v1_relat_1 @ X7)
% 0.47/0.66          | (v1_xboole_0 @ X7))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X0)
% 0.47/0.66          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.66          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.66  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0)
% 0.47/0.66          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.66          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X0)
% 0.47/0.66          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.66          | ~ (v1_relat_1 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['0', '47'])).
% 0.47/0.66  thf('49', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.66      inference('sup-', [status(thm)], ['4', '39'])).
% 0.47/0.66  thf('50', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0)
% 0.47/0.66          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.66          | ~ (v1_relat_1 @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['48', '49'])).
% 0.47/0.66  thf('51', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['50'])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      (![X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t8_boole])).
% 0.47/0.66  thf('53', plain,
% 0.47/0.66      (![X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t8_boole])).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.47/0.66        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('55', plain,
% 0.47/0.66      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.47/0.66         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.66      inference('split', [status(esa)], ['54'])).
% 0.47/0.66  thf('56', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (((X0) != (k1_xboole_0))
% 0.47/0.66           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.47/0.66           | ~ (v1_xboole_0 @ X0)))
% 0.47/0.66         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['53', '55'])).
% 0.47/0.66  thf('57', plain,
% 0.47/0.66      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.66         | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.47/0.66         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['56'])).
% 0.47/0.66  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.66  thf('59', plain,
% 0.47/0.66      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 0.47/0.66         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.66      inference('simplify_reflect+', [status(thm)], ['57', '58'])).
% 0.47/0.66  thf('60', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0))
% 0.47/0.66           | ~ (v1_xboole_0 @ X0)
% 0.47/0.66           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.47/0.66         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['52', '59'])).
% 0.47/0.66  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.66  thf('62', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.47/0.66         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['60', '61'])).
% 0.47/0.66  thf('63', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.66  thf('64', plain,
% 0.47/0.66      (![X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t8_boole])).
% 0.47/0.66  thf('65', plain,
% 0.47/0.66      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.66  thf('66', plain,
% 0.47/0.66      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.47/0.66         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('split', [status(esa)], ['54'])).
% 0.47/0.66  thf('67', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.47/0.66         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.66  thf('68', plain,
% 0.47/0.66      ((![X0 : $i, X1 : $i]:
% 0.47/0.66          (((X0) != (k1_xboole_0))
% 0.47/0.66           | ~ (v1_xboole_0 @ X0)
% 0.47/0.66           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.47/0.66           | ~ (v1_xboole_0 @ X1)))
% 0.47/0.66         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['64', '67'])).
% 0.47/0.66  thf('69', plain,
% 0.47/0.66      ((![X1 : $i]:
% 0.47/0.66          (~ (v1_xboole_0 @ X1)
% 0.47/0.66           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.47/0.66           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.47/0.66         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['68'])).
% 0.47/0.66  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.66  thf('71', plain,
% 0.47/0.66      ((![X1 : $i]:
% 0.47/0.66          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.47/0.66         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('simplify_reflect+', [status(thm)], ['69', '70'])).
% 0.47/0.66  thf('72', plain,
% 0.47/0.66      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.47/0.66         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['63', '71'])).
% 0.47/0.66  thf('73', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.66  thf('75', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.47/0.66  thf('76', plain,
% 0.47/0.66      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.47/0.66       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.66      inference('split', [status(esa)], ['54'])).
% 0.47/0.66  thf('77', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['75', '76'])).
% 0.47/0.66  thf('78', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['62', '77'])).
% 0.47/0.66  thf('79', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['51', '78'])).
% 0.47/0.66  thf('80', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.66  thf('82', plain, ($false),
% 0.47/0.66      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
