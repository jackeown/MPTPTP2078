%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dVMncr1hyy

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:27 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  175 (1889 expanded)
%              Number of leaves         :   31 ( 627 expanded)
%              Depth                    :   24
%              Number of atoms          : 1350 (15010 expanded)
%              Number of equality atoms :   99 (1446 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X50 @ X51 ) @ X52 )
        = ( k2_wellord1 @ X50 @ ( k3_xboole_0 @ X51 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf(t29_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
            = ( k2_wellord1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord1])).

thf('1',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

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

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('8',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X40 ) @ X41 )
      | ( ( k7_relat_1 @ X40 @ X41 )
        = X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('11',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X43 ) @ ( k6_relat_1 @ X42 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('14',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k7_relat_1 @ X39 @ X38 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X38 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('24',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k2_wellord1 @ X47 @ X46 )
        = ( k8_relat_1 @ X46 @ ( k7_relat_1 @ X47 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_wellord1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X37: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('30',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('31',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X35 )
      | ( ( k8_relat_1 @ X35 @ X34 )
        = X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('38',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) )
        & ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ) )).

thf('39',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X48 @ X49 ) ) @ X49 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X48 @ X49 ) ) @ ( k3_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf('44',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ X1 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ X1 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['37','48'])).

thf('50',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('52',plain,(
    ! [X32: $i] :
      ( ( ( k3_relat_1 @ X32 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('59',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X50 @ X51 ) @ X52 )
        = ( k2_wellord1 @ X50 @ ( k3_xboole_0 @ X51 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['57','66'])).

thf('68',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X40 ) @ X41 )
      | ( ( k7_relat_1 @ X40 @ X41 )
        = X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) @ sk_B )
        = ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) @ sk_B )
      = ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ sk_A ) ),
    inference('sup+',[status(thm)],['36','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('75',plain,
    ( ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('77',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('79',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X50 @ X51 ) @ X52 )
        = ( k2_wellord1 @ X50 @ ( k3_xboole_0 @ X51 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('82',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X53 @ X55 ) @ X54 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X53 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k2_wellord1 @ ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k2_wellord1 @ ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','85'])).

thf('87',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('90',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X50 @ X51 ) @ X52 )
        = ( k2_wellord1 @ X50 @ ( k3_xboole_0 @ X51 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf('91',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X53 @ X55 ) @ X54 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X53 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('92',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X48 @ X49 ) ) @ X49 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['90','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['89','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('103',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X48 @ X49 ) ) @ X49 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf('104',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( X0
        = ( k3_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('108',plain,(
    ! [X32: $i] :
      ( ( ( k3_relat_1 @ X32 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X37: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('111',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k3_relat_1 @ ( k6_relat_1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('116',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','114','115','116'])).

thf('118',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['101','117','118'])).

thf('120',plain,(
    ! [X37: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('121',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X35 )
      | ( ( k8_relat_1 @ X35 @ X34 )
        = X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['88','127','128'])).

thf('130',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['101','117','118'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['79','139'])).

thf('141',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['4','140'])).

thf('142',plain,(
    $false ),
    inference(simplify,[status(thm)],['141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dVMncr1hyy
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.10  % Solved by: fo/fo7.sh
% 0.90/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.10  % done 1178 iterations in 0.640s
% 0.90/1.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.10  % SZS output start Refutation
% 0.90/1.10  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.90/1.10  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.10  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.90/1.10  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.10  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.90/1.10  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.90/1.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.10  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.10  thf(t26_wellord1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ C ) =>
% 0.90/1.10       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.90/1.10         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.90/1.10  thf('0', plain,
% 0.90/1.10      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.90/1.10         (((k2_wellord1 @ (k2_wellord1 @ X50 @ X51) @ X52)
% 0.90/1.10            = (k2_wellord1 @ X50 @ (k3_xboole_0 @ X51 @ X52)))
% 0.90/1.10          | ~ (v1_relat_1 @ X50))),
% 0.90/1.10      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.90/1.10  thf(t29_wellord1, conjecture,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ C ) =>
% 0.90/1.10       ( ( r1_tarski @ A @ B ) =>
% 0.90/1.10         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.90/1.10           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.90/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.10    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.10        ( ( v1_relat_1 @ C ) =>
% 0.90/1.10          ( ( r1_tarski @ A @ B ) =>
% 0.90/1.10            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.90/1.10              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.90/1.10    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.90/1.10  thf('1', plain,
% 0.90/1.10      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.90/1.10         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('2', plain,
% 0.90/1.10      ((((k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.90/1.10          != (k2_wellord1 @ sk_C @ sk_A))
% 0.90/1.10        | ~ (v1_relat_1 @ sk_C))),
% 0.90/1.10      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.10  thf('3', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('4', plain,
% 0.90/1.10      (((k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.90/1.10         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['2', '3'])).
% 0.90/1.10  thf(t71_relat_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.90/1.10       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.90/1.10  thf('5', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf(d10_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.10  thf('6', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.10  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.90/1.10      inference('simplify', [status(thm)], ['6'])).
% 0.90/1.10  thf(t97_relat_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ B ) =>
% 0.90/1.10       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.90/1.10         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.90/1.10  thf('8', plain,
% 0.90/1.10      (![X40 : $i, X41 : $i]:
% 0.90/1.10         (~ (r1_tarski @ (k1_relat_1 @ X40) @ X41)
% 0.90/1.10          | ((k7_relat_1 @ X40 @ X41) = (X40))
% 0.90/1.10          | ~ (v1_relat_1 @ X40))),
% 0.90/1.10      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.90/1.10  thf('9', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['7', '8'])).
% 0.90/1.10  thf('10', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['5', '9'])).
% 0.90/1.10  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.90/1.10  thf('11', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('12', plain,
% 0.90/1.10      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['10', '11'])).
% 0.90/1.10  thf(t43_funct_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.90/1.10       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.10  thf('13', plain,
% 0.90/1.10      (![X42 : $i, X43 : $i]:
% 0.90/1.10         ((k5_relat_1 @ (k6_relat_1 @ X43) @ (k6_relat_1 @ X42))
% 0.90/1.10           = (k6_relat_1 @ (k3_xboole_0 @ X42 @ X43)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.90/1.10  thf(t94_relat_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ B ) =>
% 0.90/1.10       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.90/1.10  thf('14', plain,
% 0.90/1.10      (![X38 : $i, X39 : $i]:
% 0.90/1.10         (((k7_relat_1 @ X39 @ X38) = (k5_relat_1 @ (k6_relat_1 @ X38) @ X39))
% 0.90/1.10          | ~ (v1_relat_1 @ X39))),
% 0.90/1.10      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.90/1.10  thf('15', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.90/1.10            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['13', '14'])).
% 0.90/1.10  thf('16', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('17', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.90/1.10           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.10      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.10  thf('18', plain,
% 0.90/1.10      (![X0 : $i]: ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X0)) = (k6_relat_1 @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['12', '17'])).
% 0.90/1.10  thf('19', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf('20', plain,
% 0.90/1.10      (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.90/1.10      inference('sup+', [status(thm)], ['18', '19'])).
% 0.90/1.10  thf('21', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf('22', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['20', '21'])).
% 0.90/1.10  thf('23', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.90/1.10           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.10      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.10  thf(t18_wellord1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ B ) =>
% 0.90/1.10       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.90/1.10  thf('24', plain,
% 0.90/1.10      (![X46 : $i, X47 : $i]:
% 0.90/1.10         (((k2_wellord1 @ X47 @ X46)
% 0.90/1.10            = (k8_relat_1 @ X46 @ (k7_relat_1 @ X47 @ X46)))
% 0.90/1.10          | ~ (v1_relat_1 @ X47))),
% 0.90/1.10      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.90/1.10  thf('25', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (((k2_wellord1 @ (k6_relat_1 @ X1) @ X0)
% 0.90/1.10            = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['23', '24'])).
% 0.90/1.10  thf('26', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('27', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k2_wellord1 @ (k6_relat_1 @ X1) @ X0)
% 0.90/1.10           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.90/1.10      inference('demod', [status(thm)], ['25', '26'])).
% 0.90/1.10  thf('28', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0)
% 0.90/1.10           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X0)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['22', '27'])).
% 0.90/1.10  thf('29', plain, (![X37 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X37)) = (X37))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf('30', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.90/1.10      inference('simplify', [status(thm)], ['6'])).
% 0.90/1.10  thf(t125_relat_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ B ) =>
% 0.90/1.10       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.90/1.10         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.90/1.10  thf('31', plain,
% 0.90/1.10      (![X34 : $i, X35 : $i]:
% 0.90/1.10         (~ (r1_tarski @ (k2_relat_1 @ X34) @ X35)
% 0.90/1.10          | ((k8_relat_1 @ X35 @ X34) = (X34))
% 0.90/1.10          | ~ (v1_relat_1 @ X34))),
% 0.90/1.10      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.90/1.10  thf('32', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['30', '31'])).
% 0.90/1.10  thf('33', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['29', '32'])).
% 0.90/1.10  thf('34', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('35', plain,
% 0.90/1.10      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['33', '34'])).
% 0.90/1.10  thf('36', plain,
% 0.90/1.10      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['28', '35'])).
% 0.90/1.10  thf('37', plain,
% 0.90/1.10      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['28', '35'])).
% 0.90/1.10  thf('38', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(t20_wellord1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ B ) =>
% 0.90/1.10       ( ( r1_tarski @
% 0.90/1.10           ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) ) & 
% 0.90/1.10         ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ))).
% 0.90/1.10  thf('39', plain,
% 0.90/1.10      (![X48 : $i, X49 : $i]:
% 0.90/1.10         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X48 @ X49)) @ X49)
% 0.90/1.10          | ~ (v1_relat_1 @ X48))),
% 0.90/1.10      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.90/1.10  thf(t1_xboole_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.90/1.10       ( r1_tarski @ A @ C ) ))).
% 0.90/1.10  thf('40', plain,
% 0.90/1.10      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.90/1.10         (~ (r1_tarski @ X3 @ X4)
% 0.90/1.10          | ~ (r1_tarski @ X4 @ X5)
% 0.90/1.10          | (r1_tarski @ X3 @ X5))),
% 0.90/1.10      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.90/1.10  thf('41', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X1)
% 0.90/1.10          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.90/1.10          | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.10      inference('sup-', [status(thm)], ['39', '40'])).
% 0.90/1.10  thf('42', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.90/1.10          | ~ (v1_relat_1 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['38', '41'])).
% 0.90/1.10  thf('43', plain,
% 0.90/1.10      (![X48 : $i, X49 : $i]:
% 0.90/1.10         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X48 @ X49)) @ 
% 0.90/1.10           (k3_relat_1 @ X48))
% 0.90/1.10          | ~ (v1_relat_1 @ X48))),
% 0.90/1.10      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.90/1.10  thf('44', plain,
% 0.90/1.10      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.90/1.10         (~ (r1_tarski @ X3 @ X4)
% 0.90/1.10          | ~ (r1_tarski @ X4 @ X5)
% 0.90/1.10          | (r1_tarski @ X3 @ X5))),
% 0.90/1.10      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.90/1.10  thf('45', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X0)
% 0.90/1.10          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ X1)) @ X2)
% 0.90/1.10          | ~ (r1_tarski @ (k3_relat_1 @ X0) @ X2))),
% 0.90/1.10      inference('sup-', [status(thm)], ['43', '44'])).
% 0.90/1.10  thf('46', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X0)
% 0.90/1.10          | (r1_tarski @ 
% 0.90/1.10             (k3_relat_1 @ (k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ X1)) @ 
% 0.90/1.10             sk_B)
% 0.90/1.10          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['42', '45'])).
% 0.90/1.10  thf(dt_k2_wellord1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.90/1.10  thf('47', plain,
% 0.90/1.10      (![X44 : $i, X45 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X44) | (v1_relat_1 @ (k2_wellord1 @ X44 @ X45)))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.90/1.10  thf('48', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((r1_tarski @ 
% 0.90/1.10           (k3_relat_1 @ (k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ X1)) @ sk_B)
% 0.90/1.10          | ~ (v1_relat_1 @ X0))),
% 0.90/1.10      inference('clc', [status(thm)], ['46', '47'])).
% 0.90/1.10  thf('49', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((r1_tarski @ 
% 0.90/1.10           (k3_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)) @ sk_B)
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['37', '48'])).
% 0.90/1.10  thf('50', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('51', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (r1_tarski @ 
% 0.90/1.10          (k3_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)) @ sk_B)),
% 0.90/1.10      inference('demod', [status(thm)], ['49', '50'])).
% 0.90/1.10  thf(d6_relat_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ A ) =>
% 0.90/1.10       ( ( k3_relat_1 @ A ) =
% 0.90/1.10         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.90/1.10  thf('52', plain,
% 0.90/1.10      (![X32 : $i]:
% 0.90/1.10         (((k3_relat_1 @ X32)
% 0.90/1.10            = (k2_xboole_0 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32)))
% 0.90/1.10          | ~ (v1_relat_1 @ X32))),
% 0.90/1.10      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.90/1.10  thf(t7_xboole_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.90/1.10  thf('53', plain,
% 0.90/1.10      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.90/1.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.90/1.10  thf('54', plain,
% 0.90/1.10      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.90/1.10         (~ (r1_tarski @ X3 @ X4)
% 0.90/1.10          | ~ (r1_tarski @ X4 @ X5)
% 0.90/1.10          | (r1_tarski @ X3 @ X5))),
% 0.90/1.10      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.90/1.10  thf('55', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.90/1.10      inference('sup-', [status(thm)], ['53', '54'])).
% 0.90/1.10  thf('56', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 0.90/1.10          | ~ (v1_relat_1 @ X0)
% 0.90/1.10          | (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 0.90/1.10      inference('sup-', [status(thm)], ['52', '55'])).
% 0.90/1.10  thf('57', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((r1_tarski @ 
% 0.90/1.10           (k1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)) @ sk_B)
% 0.90/1.10          | ~ (v1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['51', '56'])).
% 0.90/1.10  thf('58', plain,
% 0.90/1.10      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['28', '35'])).
% 0.90/1.10  thf('59', plain,
% 0.90/1.10      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.90/1.10         (((k2_wellord1 @ (k2_wellord1 @ X50 @ X51) @ X52)
% 0.90/1.10            = (k2_wellord1 @ X50 @ (k3_xboole_0 @ X51 @ X52)))
% 0.90/1.10          | ~ (v1_relat_1 @ X50))),
% 0.90/1.10      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.90/1.10  thf('60', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (((k2_wellord1 @ (k6_relat_1 @ X0) @ X1)
% 0.90/1.10            = (k2_wellord1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['58', '59'])).
% 0.90/1.10  thf('61', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('62', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k2_wellord1 @ (k6_relat_1 @ X0) @ X1)
% 0.90/1.10           = (k2_wellord1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.90/1.10      inference('demod', [status(thm)], ['60', '61'])).
% 0.90/1.10  thf('63', plain,
% 0.90/1.10      (![X44 : $i, X45 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X44) | (v1_relat_1 @ (k2_wellord1 @ X44 @ X45)))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.90/1.10  thf('64', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((v1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ X1) @ X0))
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['62', '63'])).
% 0.90/1.10  thf('65', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('66', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (v1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ X1) @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['64', '65'])).
% 0.90/1.10  thf('67', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (r1_tarski @ 
% 0.90/1.10          (k1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)) @ sk_B)),
% 0.90/1.10      inference('demod', [status(thm)], ['57', '66'])).
% 0.90/1.10  thf('68', plain,
% 0.90/1.10      (![X40 : $i, X41 : $i]:
% 0.90/1.10         (~ (r1_tarski @ (k1_relat_1 @ X40) @ X41)
% 0.90/1.10          | ((k7_relat_1 @ X40 @ X41) = (X40))
% 0.90/1.10          | ~ (v1_relat_1 @ X40))),
% 0.90/1.10      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.90/1.10  thf('69', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0))
% 0.90/1.10          | ((k7_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0) @ sk_B)
% 0.90/1.10              = (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['67', '68'])).
% 0.90/1.10  thf('70', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (v1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ X1) @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['64', '65'])).
% 0.90/1.10  thf('71', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((k7_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0) @ sk_B)
% 0.90/1.10           = (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.10  thf('72', plain,
% 0.90/1.10      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.90/1.10         = (k2_wellord1 @ (k6_relat_1 @ sk_A) @ sk_A))),
% 0.90/1.10      inference('sup+', [status(thm)], ['36', '71'])).
% 0.90/1.10  thf('73', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.90/1.10           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.10      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.10  thf('74', plain,
% 0.90/1.10      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['28', '35'])).
% 0.90/1.10  thf('75', plain,
% 0.90/1.10      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k6_relat_1 @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.90/1.10  thf('76', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf('77', plain,
% 0.90/1.10      (((k1_relat_1 @ (k6_relat_1 @ sk_A)) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.90/1.10      inference('sup+', [status(thm)], ['75', '76'])).
% 0.90/1.10  thf('78', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf('79', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.90/1.10      inference('demod', [status(thm)], ['77', '78'])).
% 0.90/1.10  thf('80', plain,
% 0.90/1.10      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.90/1.10         (((k2_wellord1 @ (k2_wellord1 @ X50 @ X51) @ X52)
% 0.90/1.10            = (k2_wellord1 @ X50 @ (k3_xboole_0 @ X51 @ X52)))
% 0.90/1.10          | ~ (v1_relat_1 @ X50))),
% 0.90/1.10      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.90/1.10  thf('81', plain,
% 0.90/1.10      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['28', '35'])).
% 0.90/1.10  thf(t27_wellord1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ C ) =>
% 0.90/1.10       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.90/1.10         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.90/1.10  thf('82', plain,
% 0.90/1.10      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.90/1.10         (((k2_wellord1 @ (k2_wellord1 @ X53 @ X55) @ X54)
% 0.90/1.10            = (k2_wellord1 @ (k2_wellord1 @ X53 @ X54) @ X55))
% 0.90/1.10          | ~ (v1_relat_1 @ X53))),
% 0.90/1.10      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.90/1.10  thf('83', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (((k2_wellord1 @ (k6_relat_1 @ X0) @ X1)
% 0.90/1.10            = (k2_wellord1 @ (k2_wellord1 @ (k6_relat_1 @ X0) @ X1) @ X0))
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['81', '82'])).
% 0.90/1.10  thf('84', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('85', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k2_wellord1 @ (k6_relat_1 @ X0) @ X1)
% 0.90/1.10           = (k2_wellord1 @ (k2_wellord1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['83', '84'])).
% 0.90/1.10  thf('86', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (((k2_wellord1 @ (k6_relat_1 @ X0) @ X1)
% 0.90/1.10            = (k2_wellord1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['80', '85'])).
% 0.90/1.10  thf('87', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('88', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k2_wellord1 @ (k6_relat_1 @ X0) @ X1)
% 0.90/1.10           = (k2_wellord1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.10      inference('demod', [status(thm)], ['86', '87'])).
% 0.90/1.10  thf('89', plain,
% 0.90/1.10      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['28', '35'])).
% 0.90/1.10  thf('90', plain,
% 0.90/1.10      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.90/1.10         (((k2_wellord1 @ (k2_wellord1 @ X50 @ X51) @ X52)
% 0.90/1.10            = (k2_wellord1 @ X50 @ (k3_xboole_0 @ X51 @ X52)))
% 0.90/1.10          | ~ (v1_relat_1 @ X50))),
% 0.90/1.10      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.90/1.10  thf('91', plain,
% 0.90/1.10      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.90/1.10         (((k2_wellord1 @ (k2_wellord1 @ X53 @ X55) @ X54)
% 0.90/1.10            = (k2_wellord1 @ (k2_wellord1 @ X53 @ X54) @ X55))
% 0.90/1.10          | ~ (v1_relat_1 @ X53))),
% 0.90/1.10      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.90/1.10  thf('92', plain,
% 0.90/1.10      (![X48 : $i, X49 : $i]:
% 0.90/1.10         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X48 @ X49)) @ X49)
% 0.90/1.10          | ~ (v1_relat_1 @ X48))),
% 0.90/1.10      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.90/1.10  thf('93', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X0)
% 0.90/1.10          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ X1)) @ X2)
% 0.90/1.10          | ~ (r1_tarski @ (k3_relat_1 @ X0) @ X2))),
% 0.90/1.10      inference('sup-', [status(thm)], ['43', '44'])).
% 0.90/1.10  thf('94', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X1)
% 0.90/1.10          | (r1_tarski @ 
% 0.90/1.10             (k3_relat_1 @ (k2_wellord1 @ (k2_wellord1 @ X1 @ X0) @ X2)) @ X0)
% 0.90/1.10          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['92', '93'])).
% 0.90/1.10  thf('95', plain,
% 0.90/1.10      (![X44 : $i, X45 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X44) | (v1_relat_1 @ (k2_wellord1 @ X44 @ X45)))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.90/1.10  thf('96', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         ((r1_tarski @ 
% 0.90/1.10           (k3_relat_1 @ (k2_wellord1 @ (k2_wellord1 @ X1 @ X0) @ X2)) @ X0)
% 0.90/1.10          | ~ (v1_relat_1 @ X1))),
% 0.90/1.10      inference('clc', [status(thm)], ['94', '95'])).
% 0.90/1.10  thf('97', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         ((r1_tarski @ 
% 0.90/1.10           (k3_relat_1 @ (k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)) @ X0)
% 0.90/1.10          | ~ (v1_relat_1 @ X2)
% 0.90/1.10          | ~ (v1_relat_1 @ X2))),
% 0.90/1.10      inference('sup+', [status(thm)], ['91', '96'])).
% 0.90/1.10  thf('98', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X2)
% 0.90/1.10          | (r1_tarski @ 
% 0.90/1.10             (k3_relat_1 @ (k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)) @ X0))),
% 0.90/1.10      inference('simplify', [status(thm)], ['97'])).
% 0.90/1.10  thf('99', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         ((r1_tarski @ 
% 0.90/1.10           (k3_relat_1 @ (k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ X0)
% 0.90/1.10          | ~ (v1_relat_1 @ X2)
% 0.90/1.10          | ~ (v1_relat_1 @ X2))),
% 0.90/1.10      inference('sup+', [status(thm)], ['90', '98'])).
% 0.90/1.10  thf('100', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X2)
% 0.90/1.10          | (r1_tarski @ 
% 0.90/1.10             (k3_relat_1 @ (k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ X0))),
% 0.90/1.10      inference('simplify', [status(thm)], ['99'])).
% 0.90/1.10  thf('101', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((r1_tarski @ (k3_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 0.90/1.10           X0)
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.90/1.10      inference('sup+', [status(thm)], ['89', '100'])).
% 0.90/1.10  thf('102', plain,
% 0.90/1.10      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['28', '35'])).
% 0.90/1.10  thf('103', plain,
% 0.90/1.10      (![X48 : $i, X49 : $i]:
% 0.90/1.10         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X48 @ X49)) @ X49)
% 0.90/1.10          | ~ (v1_relat_1 @ X48))),
% 0.90/1.10      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.90/1.10  thf('104', plain,
% 0.90/1.10      (![X0 : $i, X2 : $i]:
% 0.90/1.10         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.10  thf('105', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ X1)
% 0.90/1.10          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)))
% 0.90/1.10          | ((X0) = (k3_relat_1 @ (k2_wellord1 @ X1 @ X0))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['103', '104'])).
% 0.90/1.10  thf('106', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (r1_tarski @ X0 @ (k3_relat_1 @ (k6_relat_1 @ X0)))
% 0.90/1.10          | ((X0) = (k3_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ X0) @ X0)))
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['102', '105'])).
% 0.90/1.10  thf('107', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf('108', plain,
% 0.90/1.10      (![X32 : $i]:
% 0.90/1.10         (((k3_relat_1 @ X32)
% 0.90/1.10            = (k2_xboole_0 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32)))
% 0.90/1.10          | ~ (v1_relat_1 @ X32))),
% 0.90/1.10      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.90/1.10  thf('109', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (((k3_relat_1 @ (k6_relat_1 @ X0))
% 0.90/1.10            = (k2_xboole_0 @ X0 @ (k2_relat_1 @ (k6_relat_1 @ X0))))
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['107', '108'])).
% 0.90/1.10  thf('110', plain, (![X37 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X37)) = (X37))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf('111', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('112', plain,
% 0.90/1.10      (![X0 : $i]: ((k3_relat_1 @ (k6_relat_1 @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.90/1.10  thf('113', plain,
% 0.90/1.10      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.90/1.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.90/1.10  thf('114', plain,
% 0.90/1.10      (![X0 : $i]: (r1_tarski @ X0 @ (k3_relat_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['112', '113'])).
% 0.90/1.10  thf('115', plain,
% 0.90/1.10      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['28', '35'])).
% 0.90/1.10  thf('116', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('117', plain, (![X0 : $i]: ((X0) = (k3_relat_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.10      inference('demod', [status(thm)], ['106', '114', '115', '116'])).
% 0.90/1.10  thf('118', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('119', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.90/1.10      inference('demod', [status(thm)], ['101', '117', '118'])).
% 0.90/1.10  thf('120', plain, (![X37 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X37)) = (X37))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf('121', plain,
% 0.90/1.10      (![X34 : $i, X35 : $i]:
% 0.90/1.10         (~ (r1_tarski @ (k2_relat_1 @ X34) @ X35)
% 0.90/1.10          | ((k8_relat_1 @ X35 @ X34) = (X34))
% 0.90/1.10          | ~ (v1_relat_1 @ X34))),
% 0.90/1.10      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.90/1.10  thf('122', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (~ (r1_tarski @ X0 @ X1)
% 0.90/1.10          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.90/1.10          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['120', '121'])).
% 0.90/1.10  thf('123', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.90/1.10  thf('124', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (~ (r1_tarski @ X0 @ X1)
% 0.90/1.10          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.90/1.10      inference('demod', [status(thm)], ['122', '123'])).
% 0.90/1.10  thf('125', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.90/1.10           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['119', '124'])).
% 0.90/1.10  thf('126', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k2_wellord1 @ (k6_relat_1 @ X1) @ X0)
% 0.90/1.10           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.90/1.10      inference('demod', [status(thm)], ['25', '26'])).
% 0.90/1.10  thf('127', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k2_wellord1 @ (k6_relat_1 @ X1) @ X0)
% 0.90/1.10           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['125', '126'])).
% 0.90/1.10  thf('128', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k2_wellord1 @ (k6_relat_1 @ X1) @ X0)
% 0.90/1.10           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['125', '126'])).
% 0.90/1.10  thf('129', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.90/1.10           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.90/1.10      inference('demod', [status(thm)], ['88', '127', '128'])).
% 0.90/1.10  thf('130', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf('131', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.90/1.10           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['129', '130'])).
% 0.90/1.10  thf('132', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 0.90/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.10  thf('133', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((k3_xboole_0 @ X1 @ X0)
% 0.90/1.10           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.90/1.10      inference('demod', [status(thm)], ['131', '132'])).
% 0.90/1.10  thf('134', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.90/1.10      inference('demod', [status(thm)], ['101', '117', '118'])).
% 0.90/1.10  thf('135', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.10      inference('sup+', [status(thm)], ['133', '134'])).
% 0.90/1.10  thf('136', plain,
% 0.90/1.10      (![X0 : $i, X2 : $i]:
% 0.90/1.10         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.10  thf('137', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 0.90/1.10          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['135', '136'])).
% 0.90/1.10  thf('138', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.10      inference('sup+', [status(thm)], ['133', '134'])).
% 0.90/1.10  thf('139', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.10      inference('demod', [status(thm)], ['137', '138'])).
% 0.90/1.10  thf('140', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['79', '139'])).
% 0.90/1.10  thf('141', plain,
% 0.90/1.10      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['4', '140'])).
% 0.90/1.10  thf('142', plain, ($false), inference('simplify', [status(thm)], ['141'])).
% 0.90/1.10  
% 0.90/1.10  % SZS output end Refutation
% 0.90/1.10  
% 0.90/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
